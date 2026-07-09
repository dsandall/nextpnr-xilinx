/*
 *  nextpnr -- Next Generation Place and Route
 *
 *  Copyright (C) 2019  David Shah <dave@ds0.me>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *  Core routing algorithm based on CRoute:
 *
 *     CRoute: A Fast High-quality Timing-driven Connection-based FPGA Router
 *     Dries Vercruyce, Elias Vansteenkiste and Dirk Stroobandt
 *     DOI 10.1109/FCCM.2019.00017 [PDF on SciHub]
 *
 *  Modified for the nextpnr Arch API and data structures; optimised for
 *  real-world FPGA architectures in particular ECP5 and Xilinx UltraScale+
 *
 */

#include "router2.h"
#include <algorithm>
#include <boost/container/flat_map.hpp>
#include <chrono>
#include <cstring>
#include <deque>
#include <fstream>
#include <map>
#include <queue>
#include <set>
#include <thread>
#include "log.h"
#include "nextpnr.h"
#include "router1.h"
#include "timing.h"
#include "util.h"

NEXTPNR_NAMESPACE_BEGIN

namespace {
struct Router2
{

    struct PerArcData
    {
        WireId sink_wire;
        ArcBounds bb;
        bool routed = false;
        float arc_crit = 0;
    };

    // As we allow overlap at first; the nextpnr bind functions can't be used
    // as the primary relation between arcs and wires/pips
    struct PerNetData
    {
        WireId src_wire;
        std::vector<PerArcData> arcs;
        ArcBounds bb;
        // Coordinates of the center of the net, used for the weight-to-average
        int cx, cy, hpwl;
        int total_route_us = 0;
        float max_crit = 0;
        int fail_count = 0;
        bool is_reuse = false;   // split-flow option (c): yields to fresh nets (docs/47)
    };

    struct WireScore
    {
        float cost;
        float togo_cost;
        delay_t delay;
        float total() const { return cost + togo_cost; }
    };

    struct PerWireData
    {
        // nextpnr
        WireId w;
        // net --> number of arcs; driving pip
        boost::container::flat_map<int, std::pair<int, PipId>> bound_nets;
        // Historical congestion cost
        float hist_cong_cost = 1.0;
        // Wire is unavailable as locked to another arc
        bool unavailable = false;
        // This wire has to be used for this net
        int reserved_net = -1;
        // The notional location of the wire, to guarantee thread safety
        int16_t x = 0, y = 0;
        // Visit data
        struct
        {
            bool dirty = false, visited = false;
            PipId pip;
            WireScore score;
        } visit;
    };

    float present_wire_cost(const PerWireData &w, int net_uid)
    {
        int other_sources = int(w.bound_nets.size());
        if (w.bound_nets.count(net_uid))
            other_sources -= 1;
        if (other_sources == 0)
            return 1.0f;
        else
            return 1 + other_sources * curr_cong_weight;
    }

    Context *ctx;
    Router2Cfg cfg;

    Router2(Context *ctx, const Router2Cfg &cfg) : ctx(ctx), cfg(cfg)
    {
        // docs/96: REUSE_NET yield penalty, tunable so cached routing seeds without forcing.
        if (const char *p = getenv("SPLIT_REUSE_PENALTY"))
            reuse_penalty = float(atof(p));
        // Livelock breaker (see update_congestion): on for fuzzy-hop binds, or forced
        // via SPLIT_REUSE_LIVELOCK_BREAK for plain reuse binds that hit the same class.
        livelock_break = getenv("SPLIT_REUSE_LIVELOCK_BREAK") != nullptr ||
                         getenv("SPLIT_BIND_FUZZY_HOPS") != nullptr;
    }

    float reuse_penalty = 3.0f;   // 8x deadlocked dense-CPU reuse; 3x = seed-not-force default
    bool livelock_break = false;  // docs/126: net-level yield escalation for stuck tiny overuse
    int livelock_stuck = 0;       // consecutive iters with an UNCHANGED tiny overused set
    int livelock_band = 0;        // consecutive iters with ANY tiny overuse (fallback trigger)
    int livelock_rounds = 0;      // firings since overuse last hit 0 (round 2+ rips fresh too)
    std::vector<WireId> livelock_prev; // the overused wire set being compared across iters
    int livelock_maxw = [] {           // gate: only watch for stagnation below this overuse
        const char *p = getenv("SPLIT_REUSE_LIVELOCK_MAXW");
        return p ? atoi(p) : 64;       // aes_gen cascaded into a STAGNANT 28-wire set (>8)
    }();
    int _overuse_seen = 0;        // SPLIT_DUMP_OVERUSE: iters with overuse seen, to dump once

    // D1 Phase-0 overuse-plateau diagnostic (docs/140 D1 = docs/131 Phase-0, repointed).
    // SPLIT_OVERUSE_TRACE=1: once the overused set is small (<= SPLIT_OVERUSE_TRACE_MAXW,
    // default 256), emit one machine-parseable [d1w] line per overused wire per iteration
    // (wire identity + xy + contesting nets + reuse flag) so churn-vs-capacity is
    // computable offline, and every SPLIT_OVERUSE_TRACE_EVERY banded iters (default 25)
    // dump a full snapshot: [d1o] per-wire entrance-cone capacity (demand_yield's 3-level
    // uphill cone: free/bound/reserved/unavailable counts), [d1p] cumulative per-wire
    // overuse persistence, [d1n]/[d1c] every net ever seen contesting + its cells with
    // FUZZY_HINT/X_FROZEN/bel provenance. The dump also fires just before a fatal arc
    // failure and at the iteration limit. SPLIT_ROUTER_ITER_LIMIT=N: bounded diagnostic
    // abort — the main loop otherwise never gives up on a persistent plateau (docs/126).
    // All of it is OFF unless the envs are set: zero behavior change for normal flows
    // (unset/""/"0" = off, docs/146 convention).
    static bool d1_env_flag(const char *name)
    {
        const char *p = getenv(name);
        return p != nullptr && *p != '\0' && strcmp(p, "0") != 0;
    }
    bool d1_trace = d1_env_flag("SPLIT_OVERUSE_TRACE");
    int d1_trace_maxw = [] {
        const char *p = getenv("SPLIT_OVERUSE_TRACE_MAXW");
        return p ? atoi(p) : 256;
    }();
    int d1_dump_every = [] {
        const char *p = getenv("SPLIT_OVERUSE_TRACE_EVERY");
        return p ? atoi(p) : 25;
    }();
    int d1_iter_limit = [] {
        const char *p = getenv("SPLIT_ROUTER_ITER_LIMIT");
        return p ? atoi(p) : -1;
    }();
    int d1_iter = 0;                   // current main-loop iteration (set each iter)
    int d1_band_iters = 0;             // iterations spent inside the traced band
    std::map<WireId, int> d1_wire_iters; // wire -> #iterations seen overused (in band)
    std::set<int> d1_net_udatas;       // cumulative contesting nets (udata), in band
    // Starvation-mode contention (the post-docs/134 aes_gen h2+reuse failure signature:
    // fresh arcs die of entrance starvation on the FIRST iteration, before any overuse
    // plateau forms). Every demand_yield call is one starvation event: the starved sink
    // wire, the requesting net, and the reuse nets ripped for it.
    struct D1Yield
    {
        WireId dw;
        int net;
        std::vector<int> owners;
    };
    std::vector<D1Yield> d1_yields;

    // Use 'udata' for fast net lookups and indexing
    std::vector<NetInfo *> nets_by_udata;
    std::vector<PerNetData> nets;

    bool timing_driven;

    // Criticality data from timing analysis
    NetCriticalityMap net_crit;

    void setup_nets()
    {
        const bool debug_this = false;

        // Populate per-net and per-arc structures at start of routing
        nets.resize(ctx->nets.size());
        nets_by_udata.resize(ctx->nets.size());
        size_t i = 0;
        for (auto net : sorted(ctx->nets)) {
            NetInfo *ni = net.second;
            ni->udata = i;
            nets_by_udata.at(i) = ni;
            nets.at(i).arcs.resize(ni->users.size());
            nets.at(i).is_reuse = ni->attrs.count(ctx->id("REUSE_NET")) != 0;

            // Start net bounding box at overall min/max
            nets.at(i).bb.x0 = std::numeric_limits<int>::max();
            nets.at(i).bb.x1 = std::numeric_limits<int>::min();
            nets.at(i).bb.y0 = std::numeric_limits<int>::max();
            nets.at(i).bb.y1 = std::numeric_limits<int>::min();
            nets.at(i).cx = 0;
            nets.at(i).cy = 0;

            if (ni->driver.cell != nullptr) {
                Loc drv_loc = ctx->getBelLocation(ni->driver.cell->bel);
                nets.at(i).cx += drv_loc.x;
                nets.at(i).cy += drv_loc.y;
            }

            for (size_t j = 0; j < ni->users.size(); j++) {
                auto &usr = ni->users.at(j);
                WireId src_wire = ctx->getNetinfoSourceWire(ni), dst_wire = ctx->getNetinfoSinkWire(ni, usr);
                if (debug_this)
                    std::cerr << "===> setup net: " << ni->name.c_str(ctx) <<
                                 " usr cell: " << usr.cell->name.c_str(ctx) <<
                                 " port: " << ctx->nameOf(usr.port )<< std::endl;
                nets.at(i).src_wire = src_wire;
                if (ni->driver.cell == nullptr)
                    src_wire = dst_wire;
                if (ni->driver.cell == nullptr && dst_wire == WireId())
                    continue;
                if (debug_this)
                    std::cerr << "====> src wire: " << ctx->nameOfWire(src_wire) << " dst wire: " << ctx->nameOfWire(dst_wire) << std::endl;
                if (src_wire == WireId())
                    log_error("No wire found for port %s on source cell %s.\n", ctx->nameOf(ni->driver.port),
                              ctx->nameOf(ni->driver.cell));
                if (dst_wire == WireId())
                    log_error("No wire found for port %s on destination cell %s.\n", ctx->nameOf(usr.port),
                              ctx->nameOf(usr.cell));
                nets.at(i).arcs.at(j).sink_wire = dst_wire;
                // Set bounding box for this arc
                nets.at(i).arcs.at(j).bb = ctx->getRouteBoundingBox(src_wire, dst_wire);
                // Expand net bounding box to include this arc
                nets.at(i).bb.x0 = std::min(nets.at(i).bb.x0, nets.at(i).arcs.at(j).bb.x0);
                nets.at(i).bb.x1 = std::max(nets.at(i).bb.x1, nets.at(i).arcs.at(j).bb.x1);
                nets.at(i).bb.y0 = std::min(nets.at(i).bb.y0, nets.at(i).arcs.at(j).bb.y0);
                nets.at(i).bb.y1 = std::max(nets.at(i).bb.y1, nets.at(i).arcs.at(j).bb.y1);
                // Add location to centroid sum
                Loc usr_loc = ctx->getBelLocation(usr.cell->bel);
                nets.at(i).cx += usr_loc.x;
                nets.at(i).cy += usr_loc.y;
            }
            nets.at(i).hpwl = std::max(
                    std::abs(nets.at(i).bb.y1 - nets.at(i).bb.y0) + std::abs(nets.at(i).bb.x1 - nets.at(i).bb.x0), 1);
            nets.at(i).cx /= int(ni->users.size() + 1);
            nets.at(i).cy /= int(ni->users.size() + 1);
            if (ctx->debug)
                log_info("%s: bb=(%d, %d)->(%d, %d) c=(%d, %d) hpwl=%d\n", ctx->nameOf(ni), nets.at(i).bb.x0,
                         nets.at(i).bb.y0, nets.at(i).bb.x1, nets.at(i).bb.y1, nets.at(i).cx, nets.at(i).cy,
                         nets.at(i).hpwl);
            nets.at(i).bb.x0 = std::max(nets.at(i).bb.x0 - cfg.bb_margin_x, 0);
            nets.at(i).bb.y0 = std::max(nets.at(i).bb.y0 - cfg.bb_margin_y, 0);
            nets.at(i).bb.x1 = std::min(nets.at(i).bb.x1 + cfg.bb_margin_x, ctx->getGridDimX());
            nets.at(i).bb.y1 = std::min(nets.at(i).bb.y1 + cfg.bb_margin_y, ctx->getGridDimY());
            i++;
        }
    }

    dict<WireId, int> wire_to_idx;
    std::vector<PerWireData> flat_wires;

    PerWireData &wire_data(WireId w) { return flat_wires[wire_to_idx.at(w)]; }

    void setup_wires()
    {
        // Set up per-wire structures, so that MT parts don't have to do any memory allocation
        // This is possibly quite wasteful and not cache-optimal; further consideration necessary
        for (auto wire : ctx->getWires()) {
            PerWireData pwd;
            pwd.w = wire;
            NetInfo *bound = ctx->getBoundWireNet(wire);
            if (bound != nullptr) {
                pwd.bound_nets[bound->udata] = std::make_pair(1, bound->wires.at(wire).pip);
                if (bound->wires.at(wire).strength > STRENGTH_STRONG)
                    pwd.unavailable = true;
            }

            ArcBounds wire_loc = ctx->getRouteBoundingBox(wire, wire);
            pwd.x = (wire_loc.x0 + wire_loc.x1) / 2;
            pwd.y = (wire_loc.y0 + wire_loc.y1) / 2;

            wire_to_idx[wire] = int(flat_wires.size());
            flat_wires.push_back(pwd);
        }
    }

    struct QueuedWire
    {

        explicit QueuedWire(int wire = -1, PipId pip = PipId(), Loc loc = Loc(), WireScore score = WireScore{},
                            int randtag = 0)
                : wire(wire), pip(pip), loc(loc), score(score), randtag(randtag){};

        int wire;
        PipId pip;
        Loc loc;
        WireScore score;
        int randtag = 0;

        struct Greater
        {
            bool operator()(const QueuedWire &lhs, const QueuedWire &rhs) const noexcept
            {
                float lhs_score = lhs.score.cost + lhs.score.togo_cost,
                      rhs_score = rhs.score.cost + rhs.score.togo_cost;
                return lhs_score == rhs_score ? lhs.randtag > rhs.randtag : lhs_score > rhs_score;
            }
        };
    };

    bool hit_test_pip(ArcBounds &bb, Loc l) { return l.x >= bb.x0 && l.x <= bb.x1 && l.y >= bb.y0 && l.y <= bb.y1; }

    double curr_cong_weight, hist_cong_weight, estimate_weight;

    struct ThreadContext
    {
        // Nets to route
        std::vector<NetInfo *> route_nets;
        // Nets that failed routing
        std::vector<NetInfo *> failed_nets;

        std::vector<int> route_arcs;

        std::priority_queue<QueuedWire, std::vector<QueuedWire>, QueuedWire::Greater> queue;
        // Special case where one net has multiple logical arcs to the same physical sink
        pool<WireId> processed_sinks;

        // Backwards routing
        std::queue<int> backwards_queue;

        std::vector<int> dirty_wires;

        // Thread bounding box
        ArcBounds bb;

        DeterministicRNG rng;

        // SPLIT_REUSE_DIAG counters: where do reused arcs go — pre-bound OK,
        // backwards-merge into the seeded tree, or full forward A* (and how big)?
        long dg_nets = 0, dg_arcs_ok = 0, dg_arcs_ripped = 0, dg_bwd_merge = 0;
        long dg_astar_arcs = 0, dg_astar_iters = 0, dg_boom_logged = 0;
        // why backwards merge fails: budget exhausted vs thread-bbox rejection
        long dg_bwd_budget_out = 0, dg_bwd_ttw_skip = 0, dg_chain_logged = 0;
    };

    bool thread_test_wire(ThreadContext &t, PerWireData &w)
    {
        return w.x >= t.bb.x0 && w.x <= t.bb.x1 && w.y >= t.bb.y0 && w.y <= t.bb.y1;
    }

    enum ArcRouteResult
    {
        ARC_SUCCESS,
        ARC_RETRY_WITHOUT_BB,
        ARC_FATAL,
    };

// Define to make sure we don't print in a multithreaded context
#define ARC_LOG_ERR(...)                                                                                               \
    do {                                                                                                               \
        if (is_mt)                                                                                                     \
            return ARC_FATAL;                                                                                          \
        else                                                                                                           \
            log_error(__VA_ARGS__);                                                                                    \
    } while (0)
#define ROUTE_LOG_DBG(...)                                                                                             \
    do {                                                                                                               \
        if (!is_mt && ctx->debug)                                                                                      \
            log(__VA_ARGS__);                                                                                          \
    } while (0)

    void bind_pip_internal(NetInfo *net, size_t user, int wire, PipId pip)
    {
        auto &b = flat_wires.at(wire).bound_nets[net->udata];
        ++b.first;
        if (b.first == 1) {
            b.second = pip;
        } else {
            NPNR_ASSERT(b.second == pip);
        }
    }

    void unbind_pip_internal(NetInfo *net, size_t user, WireId wire)
    {
        auto &b = wire_data(wire).bound_nets.at(net->udata);
        --b.first;
        if (b.first == 0) {
            wire_data(wire).bound_nets.erase(net->udata);
        }
    }

    // Fuzzy boundaries DEMAND-DRIVEN YIELD core (docs/126): rip the REUSE nets owning
    // `dw`'s entrance cone (3 levels uphill: bound wires, reservations, arch-bound
    // pips), releasing their arch claims + reservations; they reroute with full freedom
    // (reuse status cleared) and are requeued. SINGLE-THREADED contexts only.
    // Returns the number of nets ripped.
    int demand_yield(NetInfo *net, WireId dw)
    {
        std::set<int> owners;
        std::set<WireId> seen{dw};
        std::vector<WireId> frontier{dw};
        for (int depth = 0; depth < 3 && !frontier.empty(); depth++) {
            std::vector<WireId> next;
            for (WireId fw : frontier) {
                auto &fwd = wire_data(fw);
                for (auto bn : fwd.bound_nets)
                    if (bn.first != net->udata && nets.at(bn.first).is_reuse)
                        owners.insert(bn.first);
                if (fwd.reserved_net != -1 && fwd.reserved_net != net->udata &&
                    nets.at(fwd.reserved_net).is_reuse)
                    owners.insert(fwd.reserved_net);
                for (auto uh : ctx->getPipsUphill(fw)) {
                    NetInfo *po = ctx->getBoundPipNet(uh);
                    if (po != nullptr && po != net && nets.at(po->udata).is_reuse)
                        owners.insert(po->udata);
                    WireId sw2 = ctx->getPipSrcWire(uh);
                    if (!seen.count(sw2)) {
                        seen.insert(sw2);
                        next.push_back(sw2);
                    }
                }
            }
            frontier = next;
        }
        // D1 Phase-0: record the starvation event (even when no owner is rippable —
        // that is itself signal: the cone is owned by non-reuse/hard claims).
        if (d1_trace) {
            D1Yield ev;
            ev.dw = dw;
            ev.net = net->udata;
            ev.owners.assign(owners.begin(), owners.end());
            d1_yields.push_back(ev);
            d1_net_udatas.insert(net->udata);
            for (int ow : owners)
                d1_net_udatas.insert(ow);
        }
        for (int ow : owners) {
            NetInfo *oni = nets_by_udata.at(ow);
            log_info("fuzzy: demand yield: ripping reused net '%s' starving sink %s of '%s'\n",
                     ctx->nameOf(oni), ctx->nameOfWire(dw), ctx->nameOf(net));
            for (size_t a = 0; a < nets.at(ow).arcs.size(); a++)
                ripup_arc(oni, a);
            // release arch-level claims too (rebound nets are arch-bound)
            std::vector<WireId> awires;
            for (auto &w : oni->wires)
                awires.push_back(w.first);
            for (WireId w : awires)
                ctx->unbindWire(w);
            for (auto &ad : nets.at(ow).arcs)
                ad.routed = false;
            nets.at(ow).is_reuse = false;
            failed_nets.insert(ow);
        }
        if (!owners.empty()) {
            // clear reservations the ripped nets held anywhere near the sink
            for (WireId fw : seen) {
                auto &fwd = wire_data(fw);
                if (fwd.reserved_net != -1 && owners.count(fwd.reserved_net))
                    fwd.reserved_net = -1;
            }
        }
        return int(owners.size());
    }

    void ripup_arc(NetInfo *net, size_t user)
    {
        auto &ad = nets.at(net->udata).arcs.at(user);
        if (!ad.routed)
            return;
        WireId src = nets.at(net->udata).src_wire;
        WireId cursor = ad.sink_wire;
        while (cursor != src) {
            auto &wd = wire_data(cursor);
            // Harden (docs/102 follow-up): a routed-marked chain whose wire is not bound to
            // this net in bound_nets (seed diverged from arch pip topology) must not abort —
            // stop unwinding gracefully; the arc is treated as ripped and re-routed.
            auto fnd = wd.bound_nets.find(net->udata);
            if (fnd == wd.bound_nets.end())
                break;
            PipId pip = fnd->second.second;
            unbind_pip_internal(net, user, cursor);
            cursor = ctx->getPipSrcWire(pip);
        }
        ad.routed = false;
    }

    float score_wire_for_arc(NetInfo *net, size_t user, WireId wire, PipId pip)
    {
        auto &wd = wire_data(wire);
        auto &nd = nets.at(net->udata);
        float base_cost = ctx->getDelayNS(ctx->getPipDelay(pip).maxDelay() + ctx->getWireDelay(wire).maxDelay() +
                                          ctx->getDelayEpsilon());
        float present_cost = present_wire_cost(wd, net->udata);
        float hist_cost = wd.hist_cong_cost;
        // Split-flow option (c) (docs/47): a REUSED net pays a penalty to route onto a wire
        // some OTHER net already uses, so the cached routing SEEDS the design but the router
        // is free to deviate under contention. Too stiff (8x) deadlocks dense CPUs whose
        // reused const+signal routing collide on LUT-input site wires (docs/96) -- neither
        // side wins. SPLIT_REUSE_PENALTY tunes it (default 3x: seeded but not forced). 1.0
        // disables the yield entirely (pure PathFinder negotiation on the seeded routing).
        if (nd.is_reuse) {
            size_t others = wd.bound_nets.size() - (wd.bound_nets.count(net->udata) ? 1 : 0);
            if (others > 0)
                present_cost *= reuse_penalty;
        }
        float bias_cost = 0;
        int source_uses = 0;
        if (wd.bound_nets.count(net->udata))
            source_uses = wd.bound_nets.at(net->udata).first;
        if (timing_driven) {
            float max_bound_crit = 0;
            for (auto &bound : wd.bound_nets)
                if (bound.first != net->udata)
                    max_bound_crit = std::max(max_bound_crit, nets.at(bound.first).max_crit);
            if (max_bound_crit >= 0.8 && nd.arcs.at(user).arc_crit < (max_bound_crit + 0.01)) {
                present_cost *= 1.5;
            }
        }
        if (pip != PipId()) {
            Loc pl = ctx->getPipLocation(pip);
            bias_cost = cfg.bias_cost_factor * (base_cost / int(net->users.size())) *
                        ((std::abs(pl.x - nd.cx) + std::abs(pl.y - nd.cy)) / float(nd.hpwl));
        }
        return base_cost * hist_cost * present_cost / (1 + source_uses) + bias_cost;
    }

    float get_togo_cost(NetInfo *net, size_t user, int wire, WireId sink)
    {
        auto &wd = flat_wires[wire];
        int source_uses = 0;
        if (wd.bound_nets.count(net->udata))
            source_uses = wd.bound_nets.at(net->udata).first;
        // FIXME: timing/wirelength balance?
        return (ctx->getDelayNS(ctx->estimateDelay(wd.w, sink)) / (1 + source_uses)) + cfg.ipin_cost_adder;
    }

    bool check_arc_routing(NetInfo *net, size_t usr)
    {
        auto &ad = nets.at(net->udata).arcs.at(usr);
        WireId src_wire = nets.at(net->udata).src_wire;
        WireId cursor = ad.sink_wire;
        while (wire_data(cursor).bound_nets.count(net->udata)) {
            auto &wd = wire_data(cursor);
            if (wd.bound_nets.size() != 1)
                return false;
            auto &uh = wd.bound_nets.at(net->udata).second;
            if (uh == PipId())
                break;
            cursor = ctx->getPipSrcWire(uh);
        }
        return (cursor == src_wire);
    }

    // Returns true if a wire contains no source ports or driving pips
    bool is_wire_undriveable(WireId wire, const NetInfo *net, int iter_count = 0)
    {
        // This is specifically designed to handle a particularly icky case that the current router struggles with in
        // the nexus device,
        // C -> C lut input only
        // C; D; or F from another lut -> D lut input
        // D or M -> M ff input
        // without careful reservation of C for C lut input and D for D lut input, there is fighting for D between FF
        // and LUT
        if (iter_count > 0)
            return false; // heuristic to assume we've hit general routing
        if (wire_data(wire).reserved_net != -1 && wire_data(wire).reserved_net != net->udata)
            return true; // reserved for another net
        for (auto bp : ctx->getWireBelPins(wire))
            if ((net->driver.cell == nullptr || bp.bel == net->driver.cell->bel) &&
                ctx->getBelPinType(bp.bel, bp.pin) != PORT_IN)
                return false;
        for (auto p : ctx->getPipsUphill(wire))
            if (ctx->checkPipAvail(p)) {
                if (!is_wire_undriveable(ctx->getPipSrcWire(p), net, iter_count + 1))
                    return false;
            }
        return true;
    }

    // Find all the wires that must be used to route a given arc
    bool reserve_wires_for_arc(NetInfo *net, size_t i)
    {
        bool did_something = false;
        WireId src = ctx->getNetinfoSourceWire(net);
        WireId sink = ctx->getNetinfoSinkWire(net, net->users.at(i));
        if (sink == WireId())
            return false;
        pool<WireId> rsv;
        WireId cursor = sink;
        bool done = false;
        if (ctx->debug)
            log("reserving wires for arc %d of net %s\n", int(i), ctx->nameOf(net));
        while (!done) {
            auto &wd = wire_data(cursor);
            if (ctx->debug)
                log("      %s\n", ctx->nameOfWire(cursor));
            did_something |= (wd.reserved_net != net->udata);
            wd.reserved_net = net->udata;
            if (cursor == src)
                break;
            WireId next_cursor;
            for (auto uh : ctx->getPipsUphill(cursor)) {
                WireId w = ctx->getPipSrcWire(uh);
                if (is_wire_undriveable(w, net))
                    continue;
                if (next_cursor != WireId()) {
                    done = true;
                    break;
                }
                next_cursor = w;
            }
            if (next_cursor == WireId())
                break;
            cursor = next_cursor;
        }
        return did_something;
    }

    void find_all_reserved_wires()
    {
        // Run iteratively, as reserving wires for one net might limit choices for another
        bool did_something = false;
        do {
            did_something = false;
            for (auto net : nets_by_udata) {
                WireId src = ctx->getNetinfoSourceWire(net);
                if (src == WireId())
                    continue;
                for (size_t i = 0; i < net->users.size(); i++)
                    did_something |= reserve_wires_for_arc(net, i);
            }
        } while (did_something);
    }

    void reset_wires(ThreadContext &t)
    {
        for (auto w : t.dirty_wires) {
            flat_wires[w].visit.visited = false;
            flat_wires[w].visit.dirty = false;
            flat_wires[w].visit.pip = PipId();
            flat_wires[w].visit.score = WireScore();
        }
        t.dirty_wires.clear();
    }

    void set_visited(ThreadContext &t, int wire, PipId pip, WireScore score)
    {
        auto &v = flat_wires.at(wire).visit;
        if (!v.dirty)
            t.dirty_wires.push_back(wire);
        v.dirty = true;
        v.visited = true;
        v.pip = pip;
        v.score = score;
    }
    bool was_visited(int wire) { return flat_wires.at(wire).visit.visited; }

#ifdef ARCH_XILINX
    // Special-case constant ground/vcc routing for Xilinx devices
    void route_xilinx_const(ThreadContext &t, NetInfo *net, size_t i, int src_wire_idx, WireId dst_wire, bool is_mt,
                            bool is_bb = true)
    {
        auto &nd = nets[net->udata];
        auto &ad = nd.arcs[i];

        int backwards_iter = 0;
        int backwards_limit = 5000000;

        bool const_val = false;
        if (net->name == ctx->id("$PACKER_VCC_NET"))
            const_val = true;
        else
            NPNR_ASSERT(net->name == ctx->id("$PACKER_GND_NET"));

        for (int allowed_cong = 0; allowed_cong < 10; allowed_cong++) {
            backwards_iter = 0;
            if (!t.backwards_queue.empty()) {
                std::queue<int> new_queue;
                t.backwards_queue.swap(new_queue);
            }
            t.backwards_queue.push(wire_to_idx.at(dst_wire));
            reset_wires(t);
            while (!t.backwards_queue.empty() && backwards_iter < backwards_limit) {
                int cursor = t.backwards_queue.front();
                t.backwards_queue.pop();
                auto &cwd = flat_wires[cursor];
                PipId cpip;
                if (cwd.bound_nets.count(net->udata)) {
                    // If we can tack onto existing routing; try that
                    // Only do this if the existing routing is uncontented; however
                    int cursor2 = cursor;
                    bool bwd_merge_fail = false;
                    while (flat_wires.at(cursor2).bound_nets.count(net->udata)) {
                        if (int(flat_wires.at(cursor2).bound_nets.size()) > (allowed_cong + 1)) {
                            bwd_merge_fail = true;
                            break;
                        }
                        PipId p = flat_wires.at(cursor2).bound_nets.at(net->udata).second;
                        if (p == PipId())
                            break;
                        cursor2 = wire_to_idx.at(ctx->getPipSrcWire(p));
                    }
                    if (!bwd_merge_fail && cursor2 == src_wire_idx) {
                        // Found a path to merge to existing routing; backwards
                        cursor2 = cursor;
                        while (flat_wires.at(cursor2).bound_nets.count(net->udata)) {
                            PipId p = flat_wires.at(cursor2).bound_nets.at(net->udata).second;
                            if (p == PipId())
                                break;
                            cursor2 = wire_to_idx.at(ctx->getPipSrcWire(p));
                            set_visited(t, cursor2, p, WireScore());
                        }
                        break;
                    }
                    cpip = cwd.bound_nets.at(net->udata).second;
                }
#if 0
                log("   explore %s\n", ctx->nameOfWire(cwd.w));
#endif
                if (ctx->wireIntent(cwd.w) == (const_val ? ID_PSEUDO_VCC : ID_PSEUDO_GND)) {
#if 0
                    log("    Hit global network at %s\n", ctx->nameOfWire(cwd.w));
#endif
                    // We've hit the constant pseudo-network, continue from here
                    int cursor2 = cursor;
                    while (cursor2 != src_wire_idx) {
                        auto &c2wd = flat_wires.at(cursor2);
                        bool found = false;
                        for (auto p : ctx->getPipsUphill(c2wd.w)) {
                            if (!ctx->checkPipAvail(p) && ctx->getBoundPipNet(p) != net)
                                continue;
                            WireId src = ctx->getPipSrcWire(p);
                            if (ctx->wireIntent(src) != (const_val ? ID_PSEUDO_VCC : ID_PSEUDO_GND))
                                continue;
                            if (is_wire_undriveable(src, net))
                                continue;
                            cursor2 = wire_to_idx.at(src);
                            set_visited(t, cursor2, p, WireScore());
                            found = true;
                            break;
                        }
                        if (!found)
                            log_error("Invalid global constant node '%s'\n", ctx->nameOfWire(c2wd.w));
                    }

                    break;
                }
#if 0
                std::string name = ctx->nameOfWire(cwd.w);
                if (name.substr(int(name.size()) - 3) == "A_O") {
                    for (auto uh : ctx->getPipsUphill(flat_wires[cursor].w)) {
                        log("   %s <-- %s %d\n", ctx->nameOfWire(flat_wires[cursor].w), ctx->nameOfWire(ctx->getPipSrcWire(uh)), int(!ctx->checkPipAvail(uh) && ctx->getBoundPipNet(uh) != net));
                    }
                }
#endif
                bool did_something = false;
                for (auto uh : ctx->getPipsUphill(flat_wires[cursor].w)) {
                    did_something = true;
                    if (!ctx->checkPipAvail(uh) && ctx->getBoundPipNet(uh) != net)
                        continue;
                    if (cpip != PipId() && cpip != uh)
                        continue; // don't allow multiple pips driving a wire with a net
                    int next = wire_to_idx.at(ctx->getPipSrcWire(uh));
                    if (was_visited(next))
                        continue; // skip wires that have already been visited
                    auto &wd = flat_wires[next];
                    if (wd.unavailable)
                        continue;
                    if (wd.reserved_net != -1 && wd.reserved_net != net->udata)
                        continue;
                    if (int(wd.bound_nets.size()) > (allowed_cong + 1) ||
                        (allowed_cong == 0 && wd.bound_nets.size() == 1 && !wd.bound_nets.count(net->udata)))
                        continue; // never allow congestion in backwards routing
                    t.backwards_queue.push(next);
                    set_visited(t, next, uh, WireScore());
                }
                if (did_something)
                    ++backwards_iter;
            }
            int dst_wire_idx = wire_to_idx.at(dst_wire);
            if (was_visited(src_wire_idx)) {
                ROUTE_LOG_DBG("   Routed (backwards): ");
                int cursor_fwd = src_wire_idx;
                bind_pip_internal(net, i, src_wire_idx, PipId());
                while (was_visited(cursor_fwd)) {
                    auto &v = flat_wires.at(cursor_fwd).visit;
                    cursor_fwd = wire_to_idx.at(ctx->getPipDstWire(v.pip));
                    bind_pip_internal(net, i, cursor_fwd, v.pip);
                    if (ctx->debug) {
                        auto &wd = flat_wires.at(cursor_fwd);
                        ROUTE_LOG_DBG("      wire: %s (curr %d hist %f)\n", ctx->nameOfWire(wd.w),
                                      int(wd.bound_nets.size()) - 1, wd.hist_cong_cost);
                    }
                }
                NPNR_ASSERT(cursor_fwd == dst_wire_idx);
                ad.routed = true;
                t.processed_sinks.insert(dst_wire);
                reset_wires(t);
                return;
            }
        }
        log_error("Unrouteable %s sink %s.%s (%s)\n", ctx->nameOf(net), ctx->nameOf(net->users.at(i).cell),
                  ctx->nameOf(net->users.at(i).port), ctx->nameOfWire(dst_wire));
    }
#endif

    ArcRouteResult route_arc(ThreadContext &t, NetInfo *net, size_t i, bool is_mt, bool is_bb = true)
    {

        auto &nd = nets[net->udata];
        auto &ad = nd.arcs[i];
        auto &usr = net->users.at(i);
        ROUTE_LOG_DBG("Routing arc %d of net '%s' (%d, %d) -> (%d, %d)\n", int(i), ctx->nameOf(net), ad.bb.x0, ad.bb.y0,
                      ad.bb.x1, ad.bb.y1);
        WireId src_wire = ctx->getNetinfoSourceWire(net), dst_wire = ctx->getNetinfoSinkWire(net, usr);
        if (src_wire == WireId())
            ARC_LOG_ERR("No wire found for port %s on source cell %s.\n", ctx->nameOf(net->driver.port),
                        ctx->nameOf(net->driver.cell));
        if (dst_wire == WireId())
            ARC_LOG_ERR("No wire found for port %s on destination cell %s.\n", ctx->nameOf(usr.port),
                        ctx->nameOf(usr.cell));
        int src_wire_idx = wire_to_idx.at(src_wire);
        int dst_wire_idx = wire_to_idx.at(dst_wire);
        // Check if arc was already done _in this iteration_
        if (t.processed_sinks.count(dst_wire))
            return ARC_SUCCESS;

            // Special case
#ifdef ARCH_XILINX
        if (net->name == ctx->id("$PACKER_GND_NET") || net->name == ctx->id("$PACKER_VCC_NET")) {
            route_xilinx_const(t, net, i, src_wire_idx, dst_wire, is_mt, is_bb);
            return ARC_SUCCESS;
        }
#endif

        if (!t.queue.empty()) {
            std::priority_queue<QueuedWire, std::vector<QueuedWire>, QueuedWire::Greater> new_queue;
            t.queue.swap(new_queue);
        }
        if (!t.backwards_queue.empty()) {
            std::queue<int> new_queue;
            t.backwards_queue.swap(new_queue);
        }
        // First try strongly iteration-limited routing backwards BFS
        // this will deal with certain nets faster than forward A*
        // and comes at a minimal performance cost for the others
        // This could also be used to speed up forwards routing by a hybrid
        // bidirectional approach
        int backwards_iter = 0;
        int backwards_limit = ctx->getBelGlobalBuf(net->driver.cell->bel)
                                      ? cfg.global_backwards_max_iter
                                      : (net->users.size() > 40 ? 20 * cfg.backwards_max_iter : cfg.backwards_max_iter);
        t.backwards_queue.push(wire_to_idx.at(dst_wire));
        while (!t.backwards_queue.empty() && backwards_iter < backwards_limit) {
            int cursor = t.backwards_queue.front();
            t.backwards_queue.pop();
            auto &cwd = flat_wires[cursor];
            PipId cpip;
            if (cwd.bound_nets.count(net->udata)) {
                // If we can tack onto existing routing; try that
                // Only do this if the existing routing is uncontented; however
                int cursor2 = cursor;
                bool bwd_merge_fail = false;
                while (flat_wires.at(cursor2).bound_nets.count(net->udata)) {
                    PipId p = flat_wires.at(cursor2).bound_nets.at(net->udata).second;
                    if (p == PipId())
                        break;
                    cursor2 = wire_to_idx.at(ctx->getPipSrcWire(p));
                }
                if (!bwd_merge_fail && cursor2 == src_wire_idx) {
                    // Found a path to merge to existing routing; backwards
                    cursor2 = cursor;
                    while (flat_wires.at(cursor2).bound_nets.count(net->udata)) {
                        PipId p = flat_wires.at(cursor2).bound_nets.at(net->udata).second;
                        if (p == PipId())
                            break;
                        cursor2 = wire_to_idx.at(ctx->getPipSrcWire(p));
                        set_visited(t, cursor2, p, WireScore());
                    }
                    break;
                }
                cpip = cwd.bound_nets.at(net->udata).second;
            }
            bool did_something = false;
            for (auto uh : ctx->getPipsUphill(flat_wires[cursor].w)) {
                did_something = true;
                if (!ctx->checkPipAvail(uh) && ctx->getBoundPipNet(uh) != net)
                    continue;
                if (cpip != PipId() && cpip != uh)
                    continue; // don't allow multiple pips driving a wire with a net
                int next = wire_to_idx.at(ctx->getPipSrcWire(uh));
                if (was_visited(next))
                    continue; // skip wires that have already been visited
                auto &wd = flat_wires[next];
                if (wd.unavailable)
                    continue;
                if (wd.reserved_net != -1 && wd.reserved_net != net->udata)
                    continue;
                if (wd.bound_nets.size() > 1 || (wd.bound_nets.size() == 1 && !wd.bound_nets.count(net->udata)))
                    continue; // never allow congestion in backwards routing
                if (!thread_test_wire(t, wd)) {
                    t.dg_bwd_ttw_skip++;
                    continue; // thread safety issue
                }
                t.backwards_queue.push(next);
                set_visited(t, next, uh, WireScore());
            }
            if (did_something)
                ++backwards_iter;
        }
        if (!t.backwards_queue.empty() && backwards_iter >= backwards_limit)
            t.dg_bwd_budget_out++;
        // Check if backwards routing succeeded in reaching source
        if (was_visited(src_wire_idx)) {
            t.dg_bwd_merge++;
            ROUTE_LOG_DBG("   Routed (backwards): ");
            int cursor_fwd = src_wire_idx;
            bind_pip_internal(net, i, src_wire_idx, PipId());
            while (was_visited(cursor_fwd)) {
                auto &v = flat_wires.at(cursor_fwd).visit;
                cursor_fwd = wire_to_idx.at(ctx->getPipDstWire(v.pip));
                bind_pip_internal(net, i, cursor_fwd, v.pip);
                if (ctx->debug) {
                    auto &wd = flat_wires.at(cursor_fwd);
                    ROUTE_LOG_DBG("      wire: %s (curr %d hist %f)\n", ctx->nameOfWire(wd.w),
                                  int(wd.bound_nets.size()) - 1, wd.hist_cong_cost);
                }
            }
            NPNR_ASSERT(cursor_fwd == dst_wire_idx);
            ad.routed = true;
            t.processed_sinks.insert(dst_wire);
            reset_wires(t);
            return ARC_SUCCESS;
        }

        // Normal forwards A* routing
        t.dg_astar_arcs++;
        reset_wires(t);
        WireScore base_score;
        base_score.cost = 0;
        base_score.delay = ctx->getWireDelay(src_wire).maxDelay();
        base_score.togo_cost = get_togo_cost(net, i, src_wire_idx, dst_wire);

        // Add source wire to queue
        t.queue.push(QueuedWire(src_wire_idx, PipId(), Loc(), base_score));
        set_visited(t, src_wire_idx, PipId(), base_score);

        int toexplore = 250000 * std::max(1, (ad.bb.x1 - ad.bb.x0) + (ad.bb.y1 - ad.bb.y0));
        int iter = 0;
        int explored = 1;
        bool debug_arc = /*usr.cell->type.str(ctx).find("RAMB") != std::string::npos && (usr.port ==
                            ctx->id("ADDRATIEHIGH0") || usr.port == ctx->id("ADDRARDADDRL0"))*/
                false;

        // When running without a bounding box, the toexplore limit should be
        // suspended until a solution is reached.  Once a solution is found,
        // the toexplore limit should be used again to prevent requiring the
        // router to drain the routing queue.
        //
        // Note that is it important that the must_drain_queue be set to true
        // when running without a bb to ensure that a routing failure is
        // because there is not route, rather than just because the toexplore
        // heuristic is incorrect.
        bool must_drain_queue = !is_bb;
        // SPLIT_REUSE_DIAG: per-rejection-reason counters for this arc's A*.
        long rj_bb = 0, rj_pip = 0, rj_unavail = 0, rj_reserved = 0, rj_ownpip = 0, rj_ttw = 0;
        while (!t.queue.empty() && (must_drain_queue || iter < toexplore)) {
            auto curr = t.queue.top();
            auto &d = flat_wires.at(curr.wire);
            t.queue.pop();
            ++iter;
#if 0
            ROUTE_LOG_DBG("current wire %s\n", ctx->nameOfWire(d.w));
#endif
            // Explore all pips downhill of cursor
            for (auto dh : ctx->getPipsDownhill(d.w)) {
                // Skip pips outside of box in bounding-box mode
#if 0
                ROUTE_LOG_DBG("trying pip %s\n", ctx->nameOfPip(dh));
#endif
#if 0
                int wire_intent = ctx->wireIntent(curr.wire);
                if (is_bb && !hit_test_pip(ad.bb, ctx->getPipLocation(dh)) && wire_intent != ID_PSEUDO_GND && wire_intent != ID_PSEUDO_VCC)
                    continue;
#else
                if (is_bb && !hit_test_pip(nd.bb, ctx->getPipLocation(dh))) {
                    rj_bb++;
                    continue;
                }
                if (!ctx->checkPipAvail(dh) && ctx->getBoundPipNet(dh) != net) {
                    rj_pip++;
                    continue;
                }
#endif
                // Evaluate score of next wire
                WireId next = ctx->getPipDstWire(dh);
                int next_idx = wire_to_idx.at(next);
                if (was_visited(next_idx))
                    continue;
#if 1
                if (debug_arc)
                    ROUTE_LOG_DBG("   src wire %s\n", ctx->nameOfWire(next));
#endif
                auto &nwd = flat_wires.at(next_idx);
                if (nwd.unavailable) {
                    rj_unavail++;
                    continue;
                }
                if (nwd.reserved_net != -1 && nwd.reserved_net != net->udata) {
                    rj_reserved++;
                    continue;
                }
                if (nwd.bound_nets.count(net->udata) && nwd.bound_nets.at(net->udata).second != dh) {
                    rj_ownpip++;
                    continue;
                }
                if (!thread_test_wire(t, nwd)) {
                    rj_ttw++;
                    continue; // thread safety issue
                }
                WireScore next_score;
                next_score.cost = curr.score.cost + score_wire_for_arc(net, i, next, dh);
                next_score.delay =
                        curr.score.delay + ctx->getPipDelay(dh).maxDelay() + ctx->getWireDelay(next).maxDelay();
                next_score.togo_cost = cfg.estimate_weight * get_togo_cost(net, i, next_idx, dst_wire);
                const auto &v = nwd.visit;
                if (!v.visited || (v.score.total() > next_score.total())) {
                    ++explored;
#if 0
                    ROUTE_LOG_DBG("exploring wire %s cost %f togo %f\n", ctx->nameOfWire(next), next_score.cost,
                                  next_score.togo_cost);
#endif
                    // Add wire to queue if it meets criteria
                    t.queue.push(QueuedWire(next_idx, dh, ctx->getPipLocation(dh), next_score, t.rng.rng()));
                    set_visited(t, next_idx, dh, next_score);
                    if (next == dst_wire) {
                        toexplore = std::min(toexplore, iter + 5);
                        must_drain_queue = false;
                    }
                }
            }
        }
        t.dg_astar_iters += iter;
        // SPLIT_REUSE_DIAG: name the exploding arcs (first few per thread) — which
        // net class pays the huge A*s, and between which wires.
        static const bool dg_on = getenv("SPLIT_REUSE_DIAG") != nullptr;
        if (dg_on && iter > 20000 && t.dg_boom_logged < 8) {
            t.dg_boom_logged++;
            log_info("[reuse-diag] BOOM net=%s arc=%d iters=%d explored=%d src=%s dst=%s reuse=%d "
                     "rej{bb=%ld pip=%ld unavail=%ld resv=%ld ownpip=%ld ttw=%ld}\n",
                     ctx->nameOf(net), int(i), iter, explored,
                     ctx->nameOfWire(ctx->getNetinfoSourceWire(net)), ctx->nameOfWire(dst_wire),
                     int(nets.at(net->udata).is_reuse), rj_bb, rj_pip, rj_unavail, rj_reserved,
                     rj_ownpip, rj_ttw);
        }
        if (was_visited(dst_wire_idx)) {
            ROUTE_LOG_DBG("   Routed (explored %d wires): ", explored);
            int cursor_bwd = dst_wire_idx;
            while (was_visited(cursor_bwd)) {
                auto &v = flat_wires.at(cursor_bwd).visit;
                bind_pip_internal(net, i, cursor_bwd, v.pip);
                if (ctx->debug) {
                    auto &wd = flat_wires.at(cursor_bwd);
                    ROUTE_LOG_DBG("      wire: %s (curr %d hist %f share %d)\n", ctx->nameOfWire(wd.w),
                                  int(wd.bound_nets.size()) - 1, wd.hist_cong_cost,
                                  wd.bound_nets.count(net->udata) ? wd.bound_nets.at(net->udata).first : 0);
                }
                if (v.pip == PipId()) {
                    NPNR_ASSERT(cursor_bwd == src_wire_idx);
                    break;
                }
                ROUTE_LOG_DBG("         pip: %s (%d, %d)\n", ctx->nameOfPip(v.pip), ctx->getPipLocation(v.pip).x,
                              ctx->getPipLocation(v.pip).y);
                cursor_bwd = wire_to_idx.at(ctx->getPipSrcWire(v.pip));
            }
            t.processed_sinks.insert(dst_wire);
            ad.routed = true;
            reset_wires(t);
            return ARC_SUCCESS;
        } else {
            if (!is_bb)   // unbounded retry exhausted: name what rejected the frontier
                log_info("[fail-diag] arc %d of %s: A* drained after %d iters; "
                         "rej{bb=%ld pip=%ld unavail=%ld resv=%ld ownpip=%ld ttw=%ld}\n",
                         int(i), ctx->nameOf(net), iter, rj_bb, rj_pip, rj_unavail,
                         rj_reserved, rj_ownpip, rj_ttw);
            reset_wires(t);
            return ARC_RETRY_WITHOUT_BB;
        }
    }
#undef ARC_ERR

    bool route_net(ThreadContext &t, NetInfo *net, bool is_mt)
    {

#ifdef ARCH_ECP5
        if (net->is_global)
            return true;
#endif

        ROUTE_LOG_DBG("Routing net '%s'...\n", ctx->nameOf(net));

        auto rstart = std::chrono::high_resolution_clock::now();

        // Nothing to do if net is undriven
        if (net->driver.cell == nullptr)
            return true;

        bool have_failures = false;
        t.processed_sinks.clear();
        t.route_arcs.clear();
        for (size_t i = 0; i < net->users.size(); i++) {
            // Ripup failed arcs to start with
            // Check if arc is already legally routed
            // docs/101 §task2 / docs/102 (FIXED): an arc preserved here from the reuse
            // seed has a valid, uncontended flat_wires chain to the source — it IS routed.
            // Historically ad.routed stayed false, so bind_and_check's `!ad.routed`
            // early-out returned success WITHOUT binding → the reused sink landed UNBOUND
            // and the trailing router1 re-routed it (measured on frozen riscv reuse: router1
            // = 3380 arcs / 20.37s, 75% of nextpnr). Mark it routed so bind_and_check_all
            // commits the flat_wires chain into the Arch API; bind_and_check is hardened
            // below to fail gracefully (re-route) instead of aborting if the seeded chain
            // and the arch pip topology diverge.
            if (check_arc_routing(net, i)) {
                // Only mark a REUSE-seed arc routed (that is the case docs/102 targets: keep
                // the preserved flat_wires chain so bind_and_check_all commits it). A
                // from-scratch arc that merely re-passes this check across router2 iterations
                // must NOT be marked routed here — doing so drove ripup_arc's bound_nets.at()
                // to abort mid-route on dense gens (design-desktop repro; parent 275f2909 fine).
                if (nets.at(net->udata).is_reuse)
                    nets.at(net->udata).arcs.at(i).routed = true;
                continue;
            }
            auto &usr = net->users.at(i);
            WireId dst_wire = ctx->getNetinfoSinkWire(net, usr);
            // Case of arcs that were pre-routed strongly (e.g. clocks)
            if (net->wires.count(dst_wire) && net->wires.at(dst_wire).strength > STRENGTH_STRONG)
                return ARC_SUCCESS;
            // Ripup arc to start with
            ripup_arc(net, i);
            t.route_arcs.push_back(i);
        }
        t.dg_nets++;
        t.dg_arcs_ripped += long(t.route_arcs.size());
        t.dg_arcs_ok += long(net->users.size()) - long(t.route_arcs.size());
        // SPLIT_REUSE_DIAG: for the first few RIPPED arcs of reuse nets, walk the
        // bound chain again and log WHERE it stopped (the missing-link wire class):
        // is the seed failing at the source-side site hop, a sink-side hop, or a
        // multi-bound wire? This decides what getNetRoutingLocs should also keep.
        static const bool dg_on2 = getenv("SPLIT_REUSE_DIAG") != nullptr;
        if (dg_on2 && nets.at(net->udata).is_reuse && !t.route_arcs.empty() &&
            t.dg_chain_logged < 12) {
            t.dg_chain_logged++;
            size_t i0 = t.route_arcs.front();
            WireId src_wire = nets.at(net->udata).src_wire;
            WireId cursor = nets.at(net->udata).arcs.at(i0).sink_wire;
            int hops = 0;
            bool multi = false;
            while (wire_data(cursor).bound_nets.count(net->udata)) {
                auto &wd = wire_data(cursor);
                if (wd.bound_nets.size() != 1) { multi = true; break; }
                auto &uh = wd.bound_nets.at(net->udata).second;
                if (uh == PipId())
                    break;
                cursor = ctx->getPipSrcWire(uh);
                hops++;
            }
            log_info("[reuse-diag] CHAINSTOP net=%s arc=%d hops=%d multi=%d stop=%s src=%s sink_bound=%d\n",
                     ctx->nameOf(net), int(i0), hops, int(multi), ctx->nameOfWire(cursor),
                     ctx->nameOfWire(src_wire),
                     int(wire_data(nets.at(net->udata).arcs.at(i0).sink_wire).bound_nets.count(net->udata)));
        }
        for (auto i : t.route_arcs) {
            auto res1 = route_arc(t, net, i, is_mt, true);
            if (res1 == ARC_FATAL)
                return false; // Arc failed irrecoverably
            else if (res1 == ARC_RETRY_WITHOUT_BB) {
                if (is_mt) {
                    // Can't break out of bounding box in multi-threaded mode, so mark this arc as a failure
                    have_failures = true;
                } else {
                    // Attempt a re-route without the bounding box constraint
                    ROUTE_LOG_DBG("Rerouting arc %d of net '%s' without bounding box, possible tricky routing...\n",
                                  int(i), ctx->nameOf(net));
                    auto res2 = route_arc(t, net, i, is_mt, false);
                    // Fuzzy boundaries (docs/126): DEMAND-DRIVEN YIELD. A fresh arc's
                    // sink can be entrance-starved: every tile wire into the sink pin is
                    // arch-bound or reserved by REUSE nets rebound at pre-route (aes_gen:
                    // all 5 CLBLM_M_A* entrances owned). Arch-bound pips are hard A*
                    // rejects, so the docs/47 wire-level yield never engages. Before
                    // giving up, rip the reuse nets owning the sink's entrance cone
                    // (full-tree, reuse status cleared — they reroute with full freedom)
                    // and retry the arc once.
                    if (res2 != ARC_SUCCESS && livelock_break) {
                        WireId dw = ctx->getNetinfoSinkWire(net, net->users.at(i));
                        if (demand_yield(net, dw) > 0)
                            res2 = route_arc(t, net, i, is_mt, false);
                    }
                    // If this also fails, no choice but to give up
                    if (res2 != ARC_SUCCESS) {
                        // Forensics before dying: who owns the sink wire and every pip
                        // into it? (split-flow reuse: a frozen net hard-binding the
                        // sink's entry pip is invisible in the normal error.)
                        WireId dw = ctx->getNetinfoSinkWire(net, net->users.at(i));
                        for (auto bn : wire_data(dw).bound_nets)
                            log_info("  [fail-diag] sink wire bound by net %s\n",
                                     ctx->nameOf(nets_by_udata.at(bn.first)));
                        for (auto uh : ctx->getPipsUphill(dw)) {
                            NetInfo *own = ctx->getBoundPipNet(uh);
                            log_info("  [fail-diag] uphill pip %s avail=%d bound=%s\n", ctx->nameOfPip(uh),
                                     int(ctx->checkPipAvail(uh)), own ? ctx->nameOf(own) : "-");
                        }
                        // Walk the sink's uphill cone a few levels: the wall is often
                        // one hop above the sink (site input pip / tile CTRL wire) —
                        // print avail + owner + reservation for each candidate wire.
                        {
                            std::set<WireId> seen{dw};
                            std::vector<WireId> frontier{dw};
                            for (int depth = 1; depth <= 3 && !frontier.empty(); depth++) {
                                std::vector<WireId> next;
                                for (WireId fw : frontier) {
                                    for (auto uh : ctx->getPipsUphill(fw)) {
                                        WireId sww = ctx->getPipSrcWire(uh);
                                        if (seen.count(sww))
                                            continue;
                                        seen.insert(sww);
                                        auto &swd = wire_data(sww);
                                        std::string owners;
                                        for (auto bn : swd.bound_nets)
                                            owners += std::string(owners.empty() ? "" : ",") +
                                                      ctx->nameOf(nets_by_udata.at(bn.first));
                                        log_info("  [fail-diag] cone d%d wire %s (via %s pipavail=%d "
                                                 "hard=%d) unavail=%d resv=%s bound=[%s]\n",
                                                 depth, ctx->nameOfWire(sww), ctx->nameOfPip(uh),
                                                 int(ctx->checkPipAvail(uh)), int(ctx->usp_pip_hard_unavail(uh)),
                                                 int(swd.unavailable),
                                                 swd.reserved_net != -1 ? ctx->nameOf(nets_by_udata.at(swd.reserved_net))
                                                                        : "-",
                                                 owners.c_str());
                                        next.push_back(sww);
                                    }
                                }
                                frontier = next;
                            }
                        }
                        // Source side: can the arc even leave the driver pin?
                        WireId sw = ctx->getNetinfoSourceWire(net);
                        log_info("  [fail-diag] net has %d bound wires; src bound to net: %d\n",
                                 int(net->wires.size()), int(net->wires.count(sw)));
                        for (auto bn : wire_data(sw).bound_nets)
                            log_info("  [fail-diag] SRC wire bound by net %s\n",
                                     ctx->nameOf(nets_by_udata.at(bn.first)));
                        for (auto dh : ctx->getPipsDownhill(sw)) {
                            NetInfo *own = ctx->getBoundPipNet(dh);
                            log_info("  [fail-diag] src downhill pip %s avail=%d hard_unavail=%d bound=%s -> %s\n",
                                     ctx->nameOfPip(dh), int(ctx->checkPipAvail(dh)),
                                     int(ctx->usp_pip_hard_unavail(dh)), own ? ctx->nameOf(own) : "-",
                                     ctx->nameOfWire(ctx->getPipDstWire(dh)));
                        }
                        // D1 Phase-0: snapshot the contention state before dying so an
                        // arc-fatal end (vs a plateau) still yields the analysis dump.
                        if (d1_trace)
                            d1_dump("arc-fatal");
                        log_error("Failed to route arc %d of net '%s', from %s to %s.\n", int(i), ctx->nameOf(net),
                                  ctx->nameOfWire(ctx->getNetinfoSourceWire(net)),
                                  ctx->nameOfWire(ctx->getNetinfoSinkWire(net, net->users.at(i))));
                    }
                }
            }
        }
        if (cfg.perf_profile) {
            auto rend = std::chrono::high_resolution_clock::now();
            nets.at(net->udata).total_route_us +=
                    (std::chrono::duration_cast<std::chrono::microseconds>(rend - rstart).count());
        }
        return !have_failures;
    }
#undef ROUTE_LOG_DBG

    int total_wire_use = 0;
    int overused_wires = 0;
    int total_overuse = 0;
    std::vector<int> route_queue;
    std::set<int> failed_nets;

    // D1 Phase-0: full contention snapshot (see the knob comment near d1_trace).
    // Emitted line classes (all machine-parseable, one record per line):
    //   [d1o] currently-overused wire + its entrance-cone capacity (the SAME 3-level
    //         uphill cone demand_yield rips), each distinct wire reached classified
    //         free / bound / reserved / unavailable;
    //   [d1p] cumulative per-wire overuse persistence over the traced band;
    //   [d1n] each net ever seen contesting (reuse flag, fail count, cell counts);
    //   [d1c] that net's cells with FUZZY_HINT depth / X_FROZEN / bel provenance.
    // 3-level uphill entrance-cone capacity of `w` (demand_yield's cone): counts of the
    // distinct wires reached, classified free / bound / reserved / unavailable.
    void d1_cone(WireId w, int out[5])
    {
        out[0] = out[1] = out[2] = out[3] = out[4] = 0; // total free bound resv unavail
        std::set<WireId> seen{w};
        std::vector<WireId> frontier{w};
        for (int depth = 0; depth < 3 && !frontier.empty(); depth++) {
            std::vector<WireId> next;
            for (WireId fw : frontier) {
                for (auto uh : ctx->getPipsUphill(fw)) {
                    WireId sw = ctx->getPipSrcWire(uh);
                    if (seen.count(sw))
                        continue;
                    seen.insert(sw);
                    next.push_back(sw);
                    auto &swd = wire_data(sw);
                    out[0]++;
                    if (swd.unavailable)
                        out[4]++;
                    else if (!swd.bound_nets.empty())
                        out[2]++;
                    else if (swd.reserved_net != -1)
                        out[3]++;
                    else
                        out[1]++;
                }
            }
            frontier = next;
        }
    }

    void d1_dump(const char *reason)
    {
        log_info("[d1] DUMP reason=%s iter=%d overused=%d band_iters=%d cum_wires=%d cum_nets=%d "
                 "yield_events=%d\n",
                 reason, d1_iter, overused_wires, d1_band_iters, int(d1_wire_iters.size()),
                 int(d1_net_udatas.size()), int(d1_yields.size()));
        for (auto &wire : flat_wires) {
            if (int(wire.bound_nets.size()) <= 1)
                continue;
            int c[5];
            d1_cone(wire.w, c);
            log_info("[d1o] wire=%s x=%d y=%d nnets=%d cone_total=%d cone_free=%d cone_bound=%d "
                     "cone_resv=%d cone_unavail=%d\n",
                     ctx->nameOfWire(wire.w), wire.x, wire.y, int(wire.bound_nets.size()), c[0],
                     c[1], c[2], c[3], c[4]);
        }
        // Starvation events (demand_yield calls): requesting net, starved sink, ripped
        // owners; then per unique starved sink its CURRENT entrance-cone capacity.
        for (auto &ev : d1_yields) {
            auto &wd = wire_data(ev.dw);
            std::string os;
            for (int ow : ev.owners)
                os += std::string(os.empty() ? "" : ",") + ctx->nameOf(nets_by_udata.at(ow));
            log_info("[d1y] sink=%s x=%d y=%d net=%s nowners=%d owners=%s\n", ctx->nameOfWire(ev.dw),
                     wd.x, wd.y, ctx->nameOf(nets_by_udata.at(ev.net)), int(ev.owners.size()),
                     os.empty() ? "-" : os.c_str());
        }
        {
            std::set<WireId> sinks;
            for (auto &ev : d1_yields)
                sinks.insert(ev.dw);
            for (WireId s : sinks) {
                auto &wd = wire_data(s);
                int c[5];
                d1_cone(s, c);
                log_info("[d1s] sink=%s x=%d y=%d cone_total=%d cone_free=%d cone_bound=%d "
                         "cone_resv=%d cone_unavail=%d\n",
                         ctx->nameOfWire(s), wd.x, wd.y, c[0], c[1], c[2], c[3], c[4]);
            }
        }
        for (auto &kv : d1_wire_iters) {
            auto &wd = wire_data(kv.first);
            log_info("[d1p] wire=%s x=%d y=%d iters=%d\n", ctx->nameOfWire(kv.first), wd.x, wd.y,
                     kv.second);
        }
        IdString id_hint = ctx->id("FUZZY_HINT");
        IdString id_frozen = ctx->id("X_FROZEN");
        IdString id_orig = ctx->id("FUZZY_ORIG_BEL");
        for (int n : d1_net_udatas) {
            NetInfo *ni = nets_by_udata.at(n);
            auto &nd = nets.at(n);
            std::set<CellInfo *> cells;
            if (ni->driver.cell != nullptr)
                cells.insert(ni->driver.cell);
            for (auto &u : ni->users)
                if (u.cell != nullptr)
                    cells.insert(u.cell);
            int nhint = 0;
            for (CellInfo *c : cells)
                if (c->attrs.count(id_hint))
                    nhint++;
            log_info("[d1n] net=%s reuse=%d fail=%d driver=%s ncells=%d nhint=%d\n", ctx->nameOf(ni),
                     int(nd.is_reuse), nd.fail_count,
                     ni->driver.cell ? ctx->nameOf(ni->driver.cell) : "-", int(cells.size()), nhint);
            for (CellInfo *c : cells) {
                auto ith = c->attrs.find(id_hint);
                long hint = -1; // -1 = no hint attr; -2 = present but non-numeric (unexpected)
                if (ith != c->attrs.end())
                    hint = ith->second.is_string ? -2 : long(ith->second.as_int64());
                auto ito = c->attrs.find(id_orig);
                log_info("[d1c] net=%s cell=%s type=%s hint=%ld frozen=%d bel=%s orig=%s\n",
                         ctx->nameOf(ni), ctx->nameOf(c), c->type.c_str(ctx), hint,
                         int(c->attrs.count(id_frozen)),
                         c->bel != BelId() ? ctx->nameOfBel(c->bel) : "-",
                         (ito != c->attrs.end() && ito->second.is_string) ? ito->second.c_str() : "-");
            }
        }
        log_info("[d1] DUMP END reason=%s\n", reason);
    }

    void update_congestion()
    {
        total_overuse = 0;
        overused_wires = 0;
        total_wire_use = 0;
        failed_nets.clear();
        for (auto &wire : flat_wires) {
            total_wire_use += int(wire.bound_nets.size());
            int overuse = int(wire.bound_nets.size()) - 1;
            if (overuse > 0) {
                wire.hist_cong_cost += overuse * hist_cong_weight;
                total_overuse += overuse;
                overused_wires += 1;
                for (auto &bound : wire.bound_nets)
                    failed_nets.insert(bound.first);
            }
        }
        // One-shot diagnostic (SPLIT_DUMP_OVERUSE=1, docs/96): once overuse is small+stable,
        // categorise the overused wires (SITEWIRE vs INT) + their contending nets + reuse
        // flags, so split-flow reuse contention is visible. Prints once then disables.
        static bool _dumped = false;
        if (!_dumped && overused_wires > 0 && getenv("SPLIT_DUMP_OVERUSE")) {
            if (++_overuse_seen > 40) {
                _dumped = true;
                int nsite = 0, nint = 0, nfresh = 0, shown = 0;
                for (auto &wire : flat_wires) {
                    if (int(wire.bound_nets.size()) <= 1)
                        continue;
                    std::string wn = ctx->nameOfWire(wire.w);
                    bool site = wn.find("SITEWIRE/") != std::string::npos;
                    site ? ++nsite : ++nint;
                    bool any_fresh = false;
                    for (auto &b : wire.bound_nets)
                        any_fresh |= !nets.at(b.first).is_reuse;
                    if (any_fresh)
                        ++nfresh;
                    if (shown < 30) {
                        std::string ns;
                        for (auto &b : wire.bound_nets)
                            ns += std::string(" ") + ctx->nameOf(nets_by_udata.at(b.first)) +
                                  (nets.at(b.first).is_reuse ? "[r]" : "[FRESH]");
                        log_info("  [dump] %s:%s\n", wn.c_str(), ns.c_str());
                        ++shown;
                    }
                }
                log_info("[SPLIT_DUMP_OVERUSE] %d overused wires: SITEWIRE=%d INT=%d, "
                         "%d involve a FRESH net\n", overused_wires, nsite, nint, nfresh);
            }
        }
        // D1 Phase-0 trace (see knob comment near d1_trace): once the overused set is
        // small enough to be "the plateau", record its identity every iteration so
        // churn-vs-capacity is computable offline, and snapshot periodically.
        if (d1_trace && overused_wires > 0 && overused_wires <= d1_trace_maxw) {
            d1_band_iters++;
            for (auto &wire : flat_wires) {
                if (int(wire.bound_nets.size()) <= 1)
                    continue;
                d1_wire_iters[wire.w]++;
                std::string ns;
                for (auto &b : wire.bound_nets) {
                    d1_net_udatas.insert(b.first);
                    ns += std::string(ns.empty() ? "" : ",") + ctx->nameOf(nets_by_udata.at(b.first)) +
                          (nets.at(b.first).is_reuse ? "|r" : "|F");
                }
                log_info("[d1w] iter=%d wire=%s x=%d y=%d nets=%s\n", d1_iter,
                         ctx->nameOfWire(wire.w), wire.x, wire.y, ns.c_str());
            }
            if (d1_dump_every > 0 && (d1_band_iters % d1_dump_every) == 0)
                d1_dump("periodic");
        }
        // Fuzzy boundaries livelock breaker (docs/126): a fresh net (e.g. a moved hint
        // cell's deferred net) and a reused net can BOTH structurally need one wire
        // (xc7 BYP_* bypasses are often a pin's only entrance). The reused net yields
        // arc-locally under the penalty, but its pinned tree forces it straight back —
        // observed as overuse==1 ping-pong for 900+ iterations on cpu_farm hops=2.
        // Escalate: when overuse is TINY and stuck for LIVELOCK_ITERS, rip the contested
        // REUSED nets entirely and clear their reuse status (net-level yield: full
        // re-route freedom, no penalty steering). Gated on the fuzzy/livelock env so the
        // unset-knob flow stays bit-identical (the off-switch regression gate).
        if (livelock_break && overused_wires > 0 && overused_wires <= livelock_maxw) {
            // Stagnation detection: the SAME overused wire set persisting is the
            // livelock signature — fire at 15 identical iterations instead of a
            // blanket 60 (each farm-scale iteration costs seconds; the old threshold
            // added ~4 min of ping-pong per round before breaking).
            std::vector<WireId> cur;
            for (auto &wire : flat_wires)
                if (int(wire.bound_nets.size()) > 1)
                    cur.push_back(wire.w);
            if (cur == livelock_prev)
                livelock_stuck++;
            else {
                livelock_stuck = 1;
                livelock_prev = std::move(cur);
            }
            livelock_band++; // in the tiny-overuse band, set identical or not
        } else {
            livelock_stuck = 0;
            livelock_band = 0;
            livelock_prev.clear();
            if (overused_wires == 0)
                livelock_rounds = 0;
        }
        // Fire on a STAGNANT identical set (fast, 15 iters) or on ANY persistent
        // tiny-overuse band (40 iters): aes_gen's post-demand-yield cascade churns
        // between overlapping 28-wire sets, never identical, going nowhere.
        if (livelock_stuck >= 15 || livelock_band >= 40) {
            livelock_stuck = 0;
            livelock_band = 0;
            livelock_rounds++;
            for (auto &wire : flat_wires) {
                if (int(wire.bound_nets.size()) <= 1)
                    continue;
                std::vector<int> owners;
                for (auto &b : wire.bound_nets)
                    owners.push_back(b.first);
                for (int ow : owners) {
                    // Round 1: net-level yield for the REUSED contestants only. If the
                    // livelock survives that (fresh-vs-fresh: both trees bias their
                    // contested arc straight back), round 2+ rips EVERY contestant
                    // full-tree so PathFinder re-solves them globally instead of
                    // ping-ponging one arc.
                    if (livelock_rounds < 2 && !nets.at(ow).is_reuse)
                        continue;
                    NetInfo *oni = nets_by_udata.at(ow);
                    log_info("fuzzy: livelock breaker r%d: ripping %s net '%s' "
                             "(contested %s) — routes fresh from here\n",
                             livelock_rounds, nets.at(ow).is_reuse ? "reused" : "fresh",
                             ctx->nameOf(oni), ctx->nameOfWire(wire.w));
                    for (size_t a = 0; a < nets.at(ow).arcs.size(); a++)
                        ripup_arc(oni, a);
                    nets.at(ow).is_reuse = false;
                    failed_nets.insert(ow);
                }
            }
        }
        for (int n : failed_nets) {
            auto &net_data = nets.at(n);
            ++net_data.fail_count;
            if ((net_data.fail_count % 10) == 0) {
                // Every ten times a net fails to route, expand the bounding box to increase the search space
                net_data.bb.x0 = std::max(net_data.bb.x0 - 1, 0);
                net_data.bb.y0 = std::max(net_data.bb.y0 - 1, 0);
                net_data.bb.x1 = std::min(net_data.bb.x1 + 1, ctx->getGridDimX());
                net_data.bb.y1 = std::min(net_data.bb.y1 + 1, ctx->getGridDimY());
            }
        }
    }

    bool bind_and_check(NetInfo *net, int usr_idx)
    {
#ifdef ARCH_ECP5
        if (net->is_global)
            return true;
#endif
        bool success = true;
        auto &nd = nets.at(net->udata);
        auto &ad = nd.arcs.at(usr_idx);
        auto &usr = net->users.at(usr_idx);
        WireId src = ctx->getNetinfoSourceWire(net);
        // Skip routes with no source
        if (src == WireId())
            return true;
        WireId dst = ctx->getNetinfoSinkWire(net, usr);
        // Skip routes where the destination is already bound
        if (dst == WireId() || ctx->getBoundWireNet(dst) == net)
            return true;

        if (dst == src) {
            NetInfo *bound = ctx->getBoundWireNet(src);
            if (bound == nullptr)
                ctx->bindWire(src, net, STRENGTH_WEAK);
            else
                NPNR_ASSERT(bound == net);
            return true;
        }

        // Skip routes where there is no routing (special cases)
        if (!ad.routed) {
            if ((src == dst) && ctx->getBoundWireNet(dst) != net)
                ctx->bindWire(src, net, STRENGTH_WEAK);
            return true;
        }

        WireId cursor = dst;

        std::vector<PipId> to_bind;

        while (cursor != src) {
            if (!ctx->checkWireAvail(cursor)) {
                if (ctx->getBoundWireNet(cursor) == net)
                    break; // hit the part of the net that is already bound
                else {
                    success = false;
                    break;
                }
            }
            auto &wd = wire_data(cursor);
            if (!wd.bound_nets.count(net->udata)) {
                // docs/101 §task2: for a committed-from-reuse chain the flat_wires seed and
                // the arch getPipSrcWire topology can legitimately diverge at a wire the seed
                // never bound for this net. Rather than aborting the whole router (this used
                // to be a fatal log_error), treat the arc as uncommittable: fail gracefully
                // so it is ripped and re-routed fresh next iteration.
                if (ctx->debug)
                    log("  reuse-commit: chain diverged at %s for arc %d of %s; re-routing\n",
                        ctx->nameOfWire(cursor), usr_idx, ctx->nameOf(net));
                success = false;
                break;
            }
            auto &p = wd.bound_nets.at(net->udata).second;
            if (!ctx->checkPipAvail(p)) {
                success = false;
                break;
            } else {
                to_bind.push_back(p);
            }
            cursor = ctx->getPipSrcWire(p);
        }

        if (success) {
            if (ctx->getBoundWireNet(src) == nullptr)
                ctx->bindWire(src, net, STRENGTH_WEAK);
            for (auto tb : to_bind)
                ctx->bindPip(tb, net, STRENGTH_WEAK);
        } else {
            ripup_arc(net, usr_idx);
            failed_nets.insert(net->udata);
        }
        return success;
    }

    int arch_fail = 0;
    bool bind_and_check_all()
    {
        bool success = true;
        std::vector<WireId> net_wires;
        for (auto net : nets_by_udata) {
#ifdef ARCH_ECP5
            if (net->is_global)
                continue;
#endif
            // Ripup wires and pips used by the net in nextpnr's structures
            net_wires.clear();
            for (auto &w : net->wires) {
                if (w.second.strength <= STRENGTH_STRONG)
                    net_wires.push_back(w.first);
            }
            for (auto w : net_wires)
                ctx->unbindWire(w);
            // Bind the arcs using the routes we have discovered
            for (size_t i = 0; i < net->users.size(); i++) {
                if (!bind_and_check(net, i)) {
                    ++arch_fail;
                    success = false;
                }
            }
        }
        return success;
    }

    void write_heatmap(std::ostream &out, bool congestion = false)
    {
        std::vector<std::vector<int>> hm_xy;
        int max_x = 0, max_y = 0;
        for (auto &wd : flat_wires) {
            int val = int(wd.bound_nets.size()) - (congestion ? 1 : 0);
            if (wd.bound_nets.empty())
                continue;
            // Estimate wire location by driving pip location
            PipId drv;
            for (auto &bn : wd.bound_nets)
                if (bn.second.second != PipId()) {
                    drv = bn.second.second;
                    break;
                }
            if (drv == PipId())
                continue;
            Loc l = ctx->getPipLocation(drv);
            max_x = std::max(max_x, l.x);
            max_y = std::max(max_y, l.y);
            if (l.y >= int(hm_xy.size()))
                hm_xy.resize(l.y + 1);
            if (l.x >= int(hm_xy.at(l.y).size()))
                hm_xy.at(l.y).resize(l.x + 1);
            if (val > 0)
                hm_xy.at(l.y).at(l.x) += val;
        }
        for (int y = 0; y <= max_y; y++) {
            for (int x = 0; x <= max_x; x++) {
                if (y >= int(hm_xy.size()) || x >= int(hm_xy.at(y).size()))
                    out << "0,";
                else
                    out << hm_xy.at(y).at(x) << ",";
            }
            out << std::endl;
        }
    }
    int mid_x = 0, mid_y = 0;

    void partition_nets()
    {
        // Create a histogram of positions in X and Y positions
        std::map<int, int> cxs, cys;
        for (auto &n : nets) {
            if (n.cx != -1)
                ++cxs[n.cx];
            if (n.cy != -1)
                ++cys[n.cy];
        }
        // 4-way split for now
        int accum_x = 0, accum_y = 0;
        int halfway = int(nets.size()) / 2;
        for (auto &p : cxs) {
            if (accum_x < halfway && (accum_x + p.second) >= halfway)
                mid_x = p.first;
            accum_x += p.second;
        }
        for (auto &p : cys) {
            if (accum_y < halfway && (accum_y + p.second) >= halfway)
                mid_y = p.first;
            accum_y += p.second;
        }
        if (ctx->verbose) {
            log_info("    x splitpoint: %d\n", mid_x);
            log_info("    y splitpoint: %d\n", mid_y);
        }
        std::vector<int> bins(5, 0);
        for (auto &n : nets) {
            if (n.bb.x0 < mid_x && n.bb.x1 < mid_x && n.bb.y0 < mid_y && n.bb.y1 < mid_y)
                ++bins[0]; // TL
            else if (n.bb.x0 >= mid_x && n.bb.x1 >= mid_x && n.bb.y0 < mid_y && n.bb.y1 < mid_y)
                ++bins[1]; // TR
            else if (n.bb.x0 < mid_x && n.bb.x1 < mid_x && n.bb.y0 >= mid_y && n.bb.y1 >= mid_y)
                ++bins[2]; // BL
            else if (n.bb.x0 >= mid_x && n.bb.x1 >= mid_x && n.bb.y0 >= mid_y && n.bb.y1 >= mid_y)
                ++bins[3]; // BR
            else
                ++bins[4]; // cross-boundary
        }
        if (ctx->verbose)
            for (int i = 0; i < 5; i++)
                log_info("        bin %d N=%d\n", i, bins[i]);
    }

    void router_thread(ThreadContext &t)
    {
        // SPLIT_REUSE_DIAG: one-line running account of where arcs go (pre-bound OK /
        // backwards-merge / forward A* + its total explored iters) — the reuse-stitch
        // fast path vs the per-arc A* explosion are indistinguishable in the normal log.
        static const bool diag = getenv("SPLIT_REUSE_DIAG") != nullptr;
        for (auto n : t.route_nets) {
            bool result = route_net(t, n, true);
            if (!result)
                t.failed_nets.push_back(n);
            if (diag && (t.dg_nets % 500) == 0)
                log_info("[reuse-diag] nets=%ld arcs_ok=%ld ripped=%ld bwd_merge=%ld astar_arcs=%ld astar_iters=%ld bwd_budget_out=%ld bwd_ttw=%ld\n",
                         t.dg_nets, t.dg_arcs_ok, t.dg_arcs_ripped, t.dg_bwd_merge, t.dg_astar_arcs, t.dg_astar_iters,
                         t.dg_bwd_budget_out, t.dg_bwd_ttw_skip);
        }
        if (diag)
            log_info("[reuse-diag] FINAL nets=%ld arcs_ok=%ld ripped=%ld bwd_merge=%ld astar_arcs=%ld astar_iters=%ld bwd_budget_out=%ld bwd_ttw=%ld\n",
                     t.dg_nets, t.dg_arcs_ok, t.dg_arcs_ripped, t.dg_bwd_merge, t.dg_astar_arcs, t.dg_astar_iters,
                     t.dg_bwd_budget_out, t.dg_bwd_ttw_skip);
    }

    void do_route()
    {
        // Don't multithread if fewer than 200 nets (heuristic)
        if (route_queue.size() < 200) {
            ThreadContext st;
            st.rng.rngseed(ctx->rng64());
            st.bb = ArcBounds(0, 0, std::numeric_limits<int>::max(), std::numeric_limits<int>::max());
            for (size_t j = 0; j < route_queue.size(); j++) {
                route_net(st, nets_by_udata[route_queue[j]], false);
            }
            return;
        }
        const int Nq = 4, Nv = 2, Nh = 2;
        const int N = Nq + Nv + Nh;
        std::vector<ThreadContext> tcs(N + 1);
        for (auto &th : tcs) {
            th.rng.rngseed(ctx->rng64());
        }
        int le_x = mid_x;
        int rs_x = mid_x;
        int le_y = mid_y;
        int rs_y = mid_y;
        // Set up thread bounding boxes
        tcs.at(0).bb = ArcBounds(0, 0, mid_x, mid_y);
        tcs.at(1).bb = ArcBounds(mid_x + 1, 0, std::numeric_limits<int>::max(), le_y);
        tcs.at(2).bb = ArcBounds(0, mid_y + 1, mid_x, std::numeric_limits<int>::max());
        tcs.at(3).bb =
                ArcBounds(mid_x + 1, mid_y + 1, std::numeric_limits<int>::max(), std::numeric_limits<int>::max());

        tcs.at(4).bb = ArcBounds(0, 0, std::numeric_limits<int>::max(), mid_y);
        tcs.at(5).bb = ArcBounds(0, mid_y + 1, std::numeric_limits<int>::max(), std::numeric_limits<int>::max());

        tcs.at(6).bb = ArcBounds(0, 0, mid_x, std::numeric_limits<int>::max());
        tcs.at(7).bb = ArcBounds(mid_x + 1, 0, std::numeric_limits<int>::max(), std::numeric_limits<int>::max());

        tcs.at(8).bb = ArcBounds(0, 0, std::numeric_limits<int>::max(), std::numeric_limits<int>::max());

        for (auto n : route_queue) {
            auto &nd = nets.at(n);
            auto ni = nets_by_udata.at(n);
            int bin = N;
            // Quadrants
            if (nd.bb.x0 < le_x && nd.bb.x1 < le_x && nd.bb.y0 < le_y && nd.bb.y1 < le_y)
                bin = 0;
            else if (nd.bb.x0 >= rs_x && nd.bb.x1 >= rs_x && nd.bb.y0 < le_y && nd.bb.y1 < le_y)
                bin = 1;
            else if (nd.bb.x0 < le_x && nd.bb.x1 < le_x && nd.bb.y0 >= rs_y && nd.bb.y1 >= rs_y)
                bin = 2;
            else if (nd.bb.x0 >= rs_x && nd.bb.x1 >= rs_x && nd.bb.y0 >= rs_y && nd.bb.y1 >= rs_y)
                bin = 3;
            // Vertical split
            else if (nd.bb.y0 < le_y && nd.bb.y1 < le_y)
                bin = Nq + 0;
            else if (nd.bb.y0 >= rs_y && nd.bb.y1 >= rs_y)
                bin = Nq + 1;
            // Horizontal split
            else if (nd.bb.x0 < le_x && nd.bb.x1 < le_x)
                bin = Nq + Nv + 0;
            else if (nd.bb.x0 >= rs_x && nd.bb.x1 >= rs_x)
                bin = Nq + Nv + 1;
            tcs.at(bin).route_nets.push_back(ni);
        }
        if (ctx->verbose)
            log_info("%d/%d nets not multi-threadable\n", int(tcs.at(N).route_nets.size()), int(route_queue.size()));
        // Multithreaded part of routing - quadrants
        std::vector<std::thread> threads;
        for (int i = 0; i < Nq; i++) {
            threads.emplace_back([this, &tcs, i]() { router_thread(tcs.at(i)); });
        }
        for (auto &t : threads)
            t.join();
        threads.clear();
        // Vertical splits
        for (int i = Nq; i < Nq + Nv; i++) {
            threads.emplace_back([this, &tcs, i]() { router_thread(tcs.at(i)); });
        }
        for (auto &t : threads)
            t.join();
        threads.clear();
        // Horizontal splits
        for (int i = Nq + Nv; i < Nq + Nv + Nh; i++) {
            threads.emplace_back([this, &tcs, i]() { router_thread(tcs.at(i)); });
        }
        for (auto &t : threads)
            t.join();
        threads.clear();
        // Singlethreaded part of routing - nets that cross partitions
        // or don't fit within bounding box
        for (auto st_net : tcs.at(N).route_nets)
            route_net(tcs.at(N), st_net, false);
        // Failed nets
        for (int i = 0; i < N; i++)
            for (auto fail : tcs.at(i).failed_nets)
                route_net(tcs.at(N), fail, false);
    }

    //#define ROUTER2_STATISTICS

    void dump_statistics()
    {
#ifdef ROUTER2_STATISTICS
        int total_wires = int(flat_wires.size());
        int have_hist_cong = 0;
        int have_any_bound = 0, have_1_bound = 0, have_2_bound = 0, have_gte3_bound = 0;
        for (auto &wire : flat_wires) {
            int bound = wire.bound_nets.size();
            if (bound != 0)
                ++have_any_bound;
            if (bound == 1)
                ++have_1_bound;
            else if (bound == 2)
                ++have_2_bound;
            else if (bound >= 3)
                ++have_gte3_bound;
            if (wire.hist_cong_cost > 1.0)
                ++have_hist_cong;
        }
        log_info("Out of %d wires:\n", total_wires);
        log_info("     %d (%.02f%%) have any bound nets\n", have_any_bound, (100.0 * have_any_bound) / total_wires);
        log_info("     %d (%.02f%%) have 1 bound net\n", have_1_bound, (100.0 * have_1_bound) / total_wires);
        log_info("     %d (%.02f%%) have 2 bound nets\n", have_2_bound, (100.0 * have_2_bound) / total_wires);
        log_info("     %d (%.02f%%) have >2 bound nets\n", have_gte3_bound, (100.0 * have_gte3_bound) / total_wires);
        log_info("     %d (%.02f%%) have historical congestion\n", have_hist_cong,
                 (100.0 * have_hist_cong) / total_wires);
#endif
    }

    void operator()()
    {
        log_info("Running router2...\n");
        log_info("Setting up routing resources...\n");
        auto rstart = std::chrono::high_resolution_clock::now();
        setup_nets();
        setup_wires();
        find_all_reserved_wires();
        // Fuzzy boundaries PRE-FLIGHT STARVATION SWEEP (docs/126 fast path): an
        // entrance-starved arc otherwise burns a full A* drain (~2M nodes, seconds of
        // wall time) just to DETECT the starvation in the failure path — that drain
        // dominated the armed-mode overhead on AES (+3.7 s / +11.4 s nextpnr). Detect
        // upfront instead: any unrouted arc whose sink entrances are ALL hard-blocked
        // (pip arch-bound to another net, pip unavailable, or src wire reserved for
        // another net) gets the demand yield now, single-threaded, before the loop.
        if (livelock_break) {
            int starved = 0, ripped = 0;
            for (size_t ni_idx = 0; ni_idx < nets_by_udata.size(); ni_idx++) {
                NetInfo *ni = nets_by_udata.at(ni_idx);
                auto &nd = nets.at(ni_idx);
                // only FRESH nets are starvation victims; reuse nets' own unrouted
                // arcs (sink-remap quirks etc.) self-resolve and must not trigger
                // yields of innocent neighbours (v1 flagged 1279/2578 arcs and
                // yielded 43/108 nets — all churn, no runtime win)
                if (nd.is_reuse)
                    continue;
                for (size_t a = 0; a < nd.arcs.size(); a++) {
                    if (nd.arcs.at(a).routed)
                        continue;
                    WireId dw = nd.arcs.at(a).sink_wire;
                    if (dw == WireId())
                        continue;
                    bool any_open = false, any_pip = false;
                    for (auto uh : ctx->getPipsUphill(dw)) {
                        any_pip = true;
                        NetInfo *po = ctx->getBoundPipNet(uh);
                        if (po != nullptr && po != ni)
                            continue; // pip owned by another net: hard reject
                        if (!ctx->checkPipAvail(uh))
                            continue; // site-mux exclusivity etc.
                        auto &swd = wire_data(ctx->getPipSrcWire(uh));
                        if (swd.reserved_net != -1 && swd.reserved_net != int(ni_idx))
                            continue; // src reserved for another net
                        any_open = true;
                        break;
                    }
                    if (any_pip && !any_open) {
                        starved++;
                        ripped += demand_yield(ni, dw);
                    }
                }
            }
            if (starved)
                log_info("fuzzy: pre-flight: %d entrance-starved arc(s), %d reused net(s) yielded\n",
                         starved, ripped);
        }
        partition_nets();
        curr_cong_weight = cfg.init_curr_cong_weight;
        hist_cong_weight = cfg.hist_cong_weight;
        ThreadContext st;
        int iter = 1;

        for (size_t i = 0; i < nets_by_udata.size(); i++)
            route_queue.push_back(i);

        timing_driven = ctx->setting<bool>("timing_driven");
        // Did the final iteration's bind_and_check_all commit every arc into the Arch API
        // without a failure? If so, the trailing router1 pass enqueues nothing (see the
        // finalCheck handling after the loop) and can be skipped.
        bool last_bind_ok = false;
        log_info("Running main router loop...\n");
        do {
            d1_iter = iter; // D1 Phase-0: expose the loop iteration to update_congestion's trace
            ctx->sorted_shuffle(route_queue);

            if (timing_driven && (int(route_queue.size()) > (int(nets_by_udata.size()) / 50))) {
                // Heuristic: reduce runtime by skipping STA in the case of a "long tail" of a few
                // congested nodes
                get_criticalities(ctx, &net_crit);
                for (auto n : route_queue) {
                    IdString name = nets_by_udata.at(n)->name;
                    auto fnd = net_crit.find(name);
                    auto &net = nets.at(n);
                    net.max_crit = 0;
                    if (fnd == net_crit.end())
                        continue;
                    for (int i = 0; i < int(fnd->second.criticality.size()); i++) {
                        float c = fnd->second.criticality.at(i);
                        net.arcs.at(i).arc_crit = c;
                        net.max_crit = std::max(net.max_crit, c);
                    }
                }
                std::stable_sort(route_queue.begin(), route_queue.end(),
                                 [&](int na, int nb) { return nets.at(na).max_crit > nets.at(nb).max_crit; });
            }

#if 0
            for (size_t j = 0; j < route_queue.size(); j++) {
                route_net(st, nets_by_udata[route_queue[j]], false);
                if ((j % 1000) == 0 || j == (route_queue.size() - 1))
                    log("    routed %d/%d\n", int(j), int(route_queue.size()));
            }
#endif
            do_route();
            route_queue.clear();
            update_congestion();
#if 0
            if (iter == 1 && ctx->debug) {
                std::ofstream cong_map("cong_map_0.csv");
                write_heatmap(cong_map, true);
            }
#endif
            dump_statistics();

            if (overused_wires == 0) {
                // Try and actually bind nextpnr Arch API wires
                last_bind_ok = bind_and_check_all();
            } else {
                last_bind_ok = false;
            }
            for (auto cn : failed_nets)
                route_queue.push_back(cn);
            log_info("    iter=%d wires=%d overused=%d overuse=%d archfail=%s\n", iter, total_wire_use, overused_wires,
                     total_overuse, overused_wires > 0 ? "NA" : std::to_string(arch_fail).c_str());
            ++iter;
            // D1 Phase-0: bounded diagnostic abort. Without this the loop never gives up
            // on a persistent overuse plateau (docs/126: 150+ iters, no exit) — the limit
            // makes a failing-build experiment deterministic and cheap. Off unless set.
            if (d1_iter_limit > 0 && iter > d1_iter_limit && !failed_nets.empty()) {
                if (d1_trace)
                    d1_dump("iter-limit");
                log_error("[d1] SPLIT_ROUTER_ITER_LIMIT=%d reached with overused=%d overuse=%d — "
                          "diagnostic abort\n",
                          d1_iter_limit, overused_wires, total_overuse);
            }
            if (curr_cong_weight < 1e9)
                curr_cong_weight += cfg.curr_cong_mult;
        } while (!failed_nets.empty());
        if (cfg.perf_profile) {
            std::vector<std::pair<int, IdString>> nets_by_runtime;
            for (auto &n : nets_by_udata) {
                nets_by_runtime.emplace_back(nets.at(n->udata).total_route_us, n->name);
            }
            std::sort(nets_by_runtime.begin(), nets_by_runtime.end(), std::greater<std::pair<int, IdString>>());
            log_info("1000 slowest nets by runtime:\n");
            for (int i = 0; i < std::min(int(nets_by_runtime.size()), 1000); i++) {
                log("        %80s %6d %.1fms\n", nets_by_runtime.at(i).second.c_str(ctx),
                    int(ctx->nets.at(nets_by_runtime.at(i).second)->users.size()),
                    nets_by_runtime.at(i).first / 1000.0);
            }
        }
        auto rend = std::chrono::high_resolution_clock::now();
        log_info("Router2 time %.02fs\n", std::chrono::duration<float>(rend - rstart).count());

        // Final legality handling (docs/102). Historically router2 always re-ran the full
        // router1 (setup() re-walk of every arc + maze-reroute of any stragglers + a full
        // STA). When router2's own arch bind already succeeded for every arc (last_bind_ok),
        // router1 enqueues zero arcs, so its re-route is pure overhead — but it is also the
        // ONLY timing_analysis() in the routing flow (xilinx route() runs none), so STA must
        // still be produced when we skip it. On the reuse path this is the big win: without
        // the reuse-commit above, router1 re-routes the preserved reuse arcs (frozen riscv:
        // 3380 arcs / 20.37s); with it the bind is clean and router1 is skippable.
        //   SPLIT_FINAL_CHECK env: unset/auto/0 = skip router1 when the arch bind is clean,
        //   else run it; always/1 = legacy (always full router1); verify/2 = clean bind runs
        //   checkRoutedDesign() instead of the full router1.
        const char *fc_env = getenv("SPLIT_FINAL_CHECK");
        std::string fc = fc_env ? fc_env : "";
        int final_check = 0; // auto
        if (fc == "1" || fc == "always")
            final_check = 1;
        else if (fc == "2" || fc == "verify")
            final_check = 2;
        bool bind_clean = last_bind_ok && overused_wires == 0;

        if (final_check == 1 || !bind_clean) {
            log_info("Running router1 to check that route is legal...\n");
            router1(ctx, Router1Cfg(ctx));
        } else {
            if (final_check == 2) {
                log_info("Router2 arch bind clean; verifying via checkRoutedDesign "
                         "(skipping router1 re-route)...\n");
                if (!ctx->checkRoutedDesign())
                    log_error("Post-router2 legality verification failed despite a clean arch bind\n");
            } else {
                log_info("Router2 arch bind clean (overused=0, final bind_and_check_all ok); "
                         "skipping router1 legality re-route.\n");
            }
            // Preserve the STA that the router1 tail would otherwise have produced.
            timing_analysis(ctx, true /* slack_histogram */, true /* print_fmax */, true /* print_path */,
                            true /* warn_on_failure */);
        }
    }
};
} // namespace

void router2(Context *ctx, const Router2Cfg &cfg)
{
    Router2 rt(ctx, cfg);
    rt.ctx = ctx;
    rt();
}

Router2Cfg::Router2Cfg(Context *ctx)
{
    backwards_max_iter = ctx->setting<int>("router2/bwdMaxIter", 20);
    global_backwards_max_iter = ctx->setting<int>("router2/glbBwdMaxIter", 200);
    bb_margin_x = ctx->setting<int>("router2/bbMargin/x", 3);
    bb_margin_y = ctx->setting<int>("router2/bbMargin/y", 3);
    ipin_cost_adder = ctx->setting<float>("router2/ipinCostAdder", 0.0f);
    bias_cost_factor = ctx->setting<float>("router2/biasCostFactor", 0.25f);
    init_curr_cong_weight = ctx->setting<float>("router2/initCurrCongWeight", 0.5f);
    hist_cong_weight = ctx->setting<float>("router2/histCongWeight", 1.0f);
    curr_cong_mult = ctx->setting<float>("router2/currCongWeightMult", 2.0f);
    estimate_weight = ctx->setting<float>("router2/estimateWeight", 1.75f);
    perf_profile = ctx->setting<float>("router2/perfProfile", false);
}

NEXTPNR_NAMESPACE_END

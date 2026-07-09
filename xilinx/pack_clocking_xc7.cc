/*
 *  nextpnr -- Next Generation Place and Route
 *
 *  Copyright (C) 2019  David Shah <david@symbioticeda.com>
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
 */

#include <algorithm>
#include <boost/optional.hpp>
#include <boost/algorithm/string.hpp>
#include <iterator>
#include <queue>
#include <unordered_set>
#include "cells.h"
#include "chain_utils.h"
#include "design_utils.h"
#include "log.h"
#include "nextpnr.h"
#include "pack.h"
#include "pins.h"

NEXTPNR_NAMESPACE_BEGIN

void XC7Packer::prepare_clocking()
{
    log_info("Preparing clocking...\n");
    std::unordered_map<IdString, IdString> upgrade;
    upgrade[ctx->id("MMCME2_BASE")] = ctx->id("MMCME2_ADV");
    upgrade[ctx->id("PLLE2_BASE")] = ctx->id("PLLE2_ADV");

    for (auto cell : sorted(ctx->cells)) {
        CellInfo *ci = cell.second;
        if (upgrade.count(ci->type)) {
            IdString new_type = upgrade.at(ci->type);
            ci->type = new_type;
        } else if (ci->type == ctx->id("BUFG")) {
            ci->type = ctx->id("BUFGCTRL");
            rename_port(ctx, ci, ctx->id("I"), ctx->id("I0"));
            tie_port(ci, "CE0", true, true);
            tie_port(ci, "S0", true, true);
            tie_port(ci, "S1", false, true);
            tie_port(ci, "IGNORE0", true, true);
        } else if (ci->type == ctx->id("BUFGCE")) {
            ci->type = ctx->id("BUFGCTRL");
            rename_port(ctx, ci, ctx->id("I"), ctx->id("I0"));
            rename_port(ctx, ci, ctx->id("CE"), ctx->id("CE0"));
            tie_port(ci, "S0", true, true);
            tie_port(ci, "S1", false, true);
            tie_port(ci, "IGNORE0", true, true);
        } else if (ci->type == ctx->id("BUFGMUX") || ci->type == ctx->id("BUFGMUX_CTRL")) {
            // I same, S->S1 direct, S->S0 inverted, CE to VCC, IGNORE to GND
            ci->type = ctx->id("BUFGCTRL");
            rename_port(ctx, ci, ctx->id("S"), ctx->id("S1"));
            NetInfo *s_net = ci->ports.at(ctx->id("S1")).net;
            if (s_net != nullptr) {
                ci->ports[ctx->id("S0")].name = ctx->id("S0");
                ci->ports[ctx->id("S0")].type = PORT_IN;
                connect_port(ctx, s_net, ci, ctx->id("S0"));
                ci->params[ctx->id("IS_S0_INVERTED")] = Property(1);
            }
            tie_port(ci, "CE0", true, true);
            tie_port(ci, "CE1", true, true);
            tie_port(ci, "IGNORE0", false, false);
            tie_port(ci, "IGNORE1", false, false);
        } else if (ci->type == id_BUFH || ci->type == id_BUFHCE) {
            ci->type = id_BUFHCE_BUFHCE;
            tie_port(ci, "CE", true, true);
        }
    }
}

void XC7Packer::pack_plls()
{
    log_info("Packing PLLs...\n");

    auto set_default = [](CellInfo *ci, IdString param, const Property &value) {
        if (!ci->params.count(param))
            ci->params[param] = value;
    };

    std::unordered_map<IdString, XFormRule> pll_rules;
    pll_rules[ctx->id("MMCME2_ADV")].new_type = ctx->id("MMCME2_ADV_MMCME2_ADV");
    pll_rules[ctx->id("PLLE2_ADV")].new_type = ctx->id("PLLE2_ADV_PLLE2_ADV");
    generic_xform(pll_rules);
    for (auto cell : sorted(ctx->cells)) {
        CellInfo *ci = cell.second;
        // Preplace PLLs to make use of dedicated/short routing paths
        if (ci->type == ctx->id("MMCME2_ADV_MMCME2_ADV") || ci->type == ctx->id("PLLE2_ADV_PLLE2_ADV"))
            try_preplace(ci, ctx->id("CLKIN1"));
        if (ci->type == ctx->id("MMCME2_ADV_MMCME2_ADV")) {
            // Fixup parameters
            for (int i = 1; i <= 2; i++)
                set_default(ci, ctx->id("CLKIN" + std::to_string(i) + "_PERIOD"), Property("0.0"));
            for (int i = 0; i <= 6; i++) {
                set_default(ci, ctx->id("CLKOUT" + std::to_string(i) + "_CASCADE"), Property("FALSE"));
                set_default(ci, ctx->id("CLKOUT" + std::to_string(i) + "_DIVIDE"), Property(1));
                set_default(ci, ctx->id("CLKOUT" + std::to_string(i) + "_DUTY_CYCLE"), Property("0.5"));
                set_default(ci, ctx->id("CLKOUT" + std::to_string(i) + "_PHASE"), Property(0));
                set_default(ci, ctx->id("CLKOUT" + std::to_string(i) + "_USE_FINE_PS"), Property("FALSE"));
            }
            set_default(ci, ctx->id("COMPENSATION"), Property("INTERNAL"));

            // Fixup routing
            if (str_or_default(ci->params, ctx->id("COMPENSATION"), "INTERNAL") == "INTERNAL") {
                // Vivado's INTERNAL-compensation MMCM wires CLKFBIN <- CLKFBOUT
                // directly (golden top_bit.golden.v: `assign CLKFBIN = CLKFBOUT`).
                // The original code unconditionally tied CLKFBIN to VCC, which
                // leaves the PLL feedback loop OPEN -> the MMCM never locks on
                // silicon (skew-db, docs). Only tie off when the user left CLKFBIN
                // unconnected; preserve an explicit feedback so the loop can close.
                if (get_net_or_empty(ci, ctx->id("CLKFBIN")) == nullptr) {
                    disconnect_port(ctx, ci, ctx->id("CLKFBIN"));
                    connect_port(ctx, ctx->nets[ctx->id("$PACKER_VCC_NET")].get(), ci, ctx->id("CLKFBIN"));
                }
            }
        }
    }
}

void XC7Packer::pack_gbs()
{
    log_info("Packing global buffers...\n");

    // Make sure prerequisites are set up first
    for (auto cell : sorted(ctx->cells)) {
        CellInfo *ci = cell.second;
        if (ci->type == ctx->id("PS7_PS7"))
            preplace_unique(ci);
        if (ci->type == ctx->id("PCIE_2_1_PCIE_2_1"))
            preplace_unique(ci);
    }

    // Preplace global buffers to make use of dedicated/short routing
    for (auto cell : sorted(ctx->cells)) {
        CellInfo *ci = cell.second;
        if (ci->type == id_BUFGCTRL)
            try_preplace(ci, id_I0);
        if (ci->type == id_BUFG_BUFG)
            try_preplace(ci, id_I);
        if (ci->type == id_BUFHCE_BUFHCE)
            try_preplace(ci, id_I);
    }
}

void XC7Packer::pack_clocking()
{
    pack_plls();
    pack_gbs();
}

void XC7Packer::propagate_clock_constraints()
{
    // create_clock lands on the top port net (the XDC is parsed pre-pack), but the
    // domain STA actually times is the net behind the IBUF -> BUFG chain. Upstream
    // nextpnr copies clkconstr through the global buffers on ice40 (pack.cc SB_GB /
    // insert_global); the xilinx arch never did, so the derived clock net silently
    // fell back to the --freq default (12 MHz) and the XDC period was fiction for
    // the real datapath (docs/54, split-flow D6). Copy constraints forward through
    // 1:1 clock buffers to a fixpoint. Period-transforming cells (PLL/MMCM, BUFR
    // with a divide) are deliberately NOT crossed: their output periods are derived,
    // not equal, and are out of scope here.
    log_info("Propagating clock constraints through clock buffers...\n");
    int copied = 0;
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto cell : sorted(ctx->cells)) {
            CellInfo *ci = cell.second;
            const std::string type = ci->type.str(ctx);
            // (input pin, output pin) pairs this cell forwards a clock through 1:1
            std::vector<std::pair<IdString, IdString>> pairs;
            if (ci->type == id_BUFGCTRL) {
                pairs.emplace_back(ctx->id("I0"), ctx->id("O"));
                pairs.emplace_back(ctx->id("I1"), ctx->id("O"));
            } else if (ci->type == id_BUFG_BUFG || ci->type == id_BUFHCE_BUFHCE) {
                pairs.emplace_back(ctx->id("I"), ctx->id("O"));
            } else if (type.find("INBUF") != std::string::npos) {
                // IOB33[MS]?_INBUF_EN / IOB18[MS]?_INBUF_DCIEN (post-decompose_iob)
                pairs.emplace_back(ctx->id("PAD"), ctx->id("OUT"));
            } else {
                continue;
            }
            for (auto &p : pairs) {
                NetInfo *in = get_net_or_empty(ci, p.first);
                NetInfo *out = get_net_or_empty(ci, p.second);
                if (in == nullptr || out == nullptr || in->clkconstr == nullptr || out->clkconstr != nullptr)
                    continue;
                out->clkconstr = std::unique_ptr<ClockConstraint>(new ClockConstraint());
                out->clkconstr->period = in->clkconstr->period;
                out->clkconstr->high = in->clkconstr->high;
                out->clkconstr->low = in->clkconstr->low;
                log_info("    net '%s' gets period %.2f ns (%.2f MHz) through %s '%s'\n", out->name.c_str(ctx),
                         ctx->getDelayNS(out->clkconstr->period.minDelay()),
                         1000.0 / ctx->getDelayNS(out->clkconstr->period.minDelay()), type.c_str(),
                         ci->name.c_str(ctx));
                copied++;
                changed = true;
            }
        }
    }
    if (copied == 0)
        log_info("    no clock constraints to propagate\n");
}

NEXTPNR_NAMESPACE_END

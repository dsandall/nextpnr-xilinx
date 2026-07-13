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
 */

#include "json_frontend.h"
#include "frontend_base.h"
#include "json11.hpp"
#include "log.h"
#include "nextpnr.h"

#include <fstream>
#include <streambuf>
#include <unordered_map>
#include <unordered_set>

NEXTPNR_NAMESPACE_BEGIN

using namespace json11;

struct JsonFrontendImpl
{
    // See specification in frontend_base.h
    JsonFrontendImpl(Json &root) : root(root){};
    Json &root;
    typedef const Json &ModuleDataType;
    typedef const Json &ModulePortDataType;
    typedef const Json &CellDataType;
    typedef const Json &NetnameDataType;
    typedef const Json::array &BitVectorDataType;

    template <typename TFunc> void foreach_module(TFunc Func) const
    {
        for (const auto &mod : root.object_items())
            Func(mod.first, mod.second);
    }

    template <typename TFunc> void foreach_port(ModuleDataType &mod, TFunc Func) const
    {
        const auto &ports = mod["ports"];
        if (ports.is_null())
            return;
        for (const auto &port : ports.object_items())
            Func(port.first, port.second);
    }

    template <typename TFunc> void foreach_cell(ModuleDataType &mod, TFunc Func) const
    {
        const auto &cells = mod["cells"];
        if (cells.is_null())
            return;
        for (const auto &cell : cells.object_items())
            Func(cell.first, cell.second);
    }

    template <typename TFunc> void foreach_netname(ModuleDataType &mod, TFunc Func) const
    {
        const auto &netnames = mod["netnames"];
        if (netnames.is_null())
            return;
        for (const auto &netname : netnames.object_items())
            Func(netname.first, netname.second);
    }

    PortType lookup_portdir(const std::string &dir) const
    {
        if (dir == "input")
            return PORT_IN;
        else if (dir == "inout")
            return PORT_INOUT;
        else if (dir == "output")
            return PORT_OUT;
        else
            NPNR_ASSERT_FALSE("invalid json port direction");
    }

    PortType get_port_dir(ModulePortDataType &port) const { return lookup_portdir(port["direction"].string_value()); }

    int get_array_offset(const Json &obj) const
    {
        auto offset = obj["offset"];
        return offset.is_null() ? 0 : offset.int_value();
    }

    bool is_array_upto(const Json &obj) const
    {
        auto upto = obj["upto"];
        return upto.is_null() ? false : bool(upto.int_value());
    }

    BitVectorDataType &get_port_bits(ModulePortDataType &port) const { return port["bits"].array_items(); }

    const std::string &get_cell_type(CellDataType &cell) const { return cell["type"].string_value(); }

    Property parse_property(const Json &val) const
    {
        if (val.is_number()) {
            if (val.int_value() != val.number_value())
                log_error("Found an out-of-range integer parameter in the JSON file.\n"
                          "Please regenerate the input file with an up-to-date version of yosys.\n");
            return Property(val.int_value(), 32);
        } else {
            return Property::from_string(val.string_value());
        }
    }

    template <typename TFunc> void foreach_attr(const Json &obj, TFunc Func) const
    {
        const auto &attrs = obj["attributes"];
        if (attrs.is_null())
            return;
        for (const auto &attr : attrs.object_items()) {
            Func(attr.first, parse_property(attr.second));
        }
    }

    template <typename TFunc> void foreach_param(const Json &obj, TFunc Func) const
    {
        const auto &params = obj["parameters"];
        if (params.is_null())
            return;
        for (const auto &param : params.object_items()) {
            Func(param.first, parse_property(param.second));
        }
    }

    template <typename TFunc> void foreach_setting(const Json &obj, TFunc Func) const
    {
        const auto &settings = obj["settings"];
        if (settings.is_null())
            return;
        for (const auto &setting : settings.object_items()) {
            Func(setting.first, parse_property(setting.second));
        }
    }

    template <typename TFunc> void foreach_port_dir(CellDataType &cell, TFunc Func) const
    {
        for (const auto &pdir : cell["port_directions"].object_items())
            Func(pdir.first, lookup_portdir(pdir.second.string_value()));
    }

    template <typename TFunc> void foreach_port_conn(CellDataType &cell, TFunc Func) const
    {
        for (const auto &pconn : cell["connections"].object_items())
            Func(pconn.first, pconn.second.array_items());
    }

    BitVectorDataType &get_net_bits(NetnameDataType &net) const { return net["bits"].array_items(); }

    int get_vector_length(BitVectorDataType &bits) const { return int(bits.size()); }

    bool is_vector_bit_constant(BitVectorDataType &bits, int i) const
    {
        NPNR_ASSERT(i < int(bits.size()));
        return bits[i].is_string();
    }

    char get_vector_bit_constval(BitVectorDataType &bits, int i) const
    {
        auto s = bits.at(i).string_value();
        NPNR_ASSERT(s.size() == 1);
        return s.at(0);
    }

    int get_vector_bit_signal(BitVectorDataType &bits, int i) const
    {
        NPNR_ASSERT(bits.at(i).is_number());
        return bits.at(i).int_value();
    }
};

// ── split-flow D2 step 1: engine-native frozen-gen splice (`--import-frozen`) ─────────
// C++ port of the bind's Python pre-splice (toolchains/openshort/split_flow/bind/
// combine_frozen.py, docs/93 Option 3). Each frozen gen is an already-PACKED placed+
// routed netlist (freeze_gen.py output) — yosys cannot re-read a packed netlist
// (docs/93 §6.2), so the splice happens on the parsed JSON tree here, BEFORE the
// generic frontend imports the design:
//   * the gen's internal bit ids are renumbered to fresh ids disjoint from the checker;
//     its boundary PORT bits are mapped onto the blackbox instance's checker bits, so
//     each boundary net is ONE net across gen+checker.
//   * gen cells/netnames are spliced in under an "<instance>." prefix (attributes —
//     NEXTPNR_BEL / BEL_STRENGTH / ROUTING_LOCS / X_FROZEN — carried untouched); the
//     blackbox instance and the wrapper module defs are dropped.
//   * const network: $PACKER_{GND,VCC}_{DRV,NET} stay CANONICAL (unprefixed, first gen
//     wins — every gen ships its DRV at the same singleton PSEUDO BEL); later gens'
//     const bits are pre-aliased onto the canonical combined bits and their reused
//     ROUTING_LOCS unioned (dedup by "wt,wi" wire key).
// Fresh-id numeric values are assigned in json11's sorted-key order (the Python assigns
// in file order); they are invisible provided every renumbered bit carries a netname —
// otherwise the frontend would mint a "$frontend$<bit>" net NAME from the id. The
// splice warns loudly if that ever happens (identity-at-risk).
// NOTE (docs/134 lesson / full-D2 headroom): this step splices the same JSON facts the
// Python did — packer state that never reaches the JSON (constr_parent macro bindings)
// is equally absent from both paths. A later D2 step can extend the frozen JSON with
// those facts and consume them HERE, natively, without another pipeline stage.

static bool attr_true(const Json &val)
{
    if (val.is_null())
        return false;
    if (val.is_number())
        return val.int_value() != 0;
    // yosys writes attribute ints as bit strings, e.g. "000...001"
    return val.string_value().find('1') != std::string::npos;
}

static Json::object obj_items(const Json &j) { return j.is_object() ? j.object_items() : Json::object{}; }

static bool is_const_drv(const std::string &n) { return n == "$PACKER_GND_DRV" || n == "$PACKER_VCC_DRV"; }
static bool is_const_net(const std::string &n) { return n == "$PACKER_GND_NET" || n == "$PACKER_VCC_NET"; }

// "wt,wi" key of one ROUTING_LOCS entry (everything before the second comma)
static std::string routing_wire_key(const std::string &entry)
{
    size_t c1 = entry.find(',');
    if (c1 == std::string::npos)
        return entry;
    size_t c2 = entry.find(',', c1 + 1);
    return entry.substr(0, c2 == std::string::npos ? std::string::npos : c2);
}

static Json splice_frozen_gens(const Json &modroot, const std::vector<std::string> &specs)
{
    Json::object mods = modroot.object_items();
    // the checker top = the module with a truthy (* top *) attribute (yosys synth sets it)
    std::string topname;
    for (auto &kv : mods) {
        const Json &attrs = kv.second["attributes"];
        if (attr_true(attrs["top"]) && !attr_true(attrs["blackbox"])) {
            if (!topname.empty())
                log_error("[import-frozen] multiple (* top *) modules: '%s' and '%s'\n", topname.c_str(),
                          kv.first.c_str());
            topname = kv.first;
        }
    }
    if (topname.empty())
        log_error("[import-frozen] no module with a (* top *) attribute in the --json input\n");
    Json::object top = obj_items(mods.at(topname));
    Json::object topcells = obj_items(top["cells"]);
    Json::object topnets = obj_items(top["netnames"]);

    // next fresh bit id = 1 + max int bit anywhere in the checker top
    int next_bit = 0;
    auto scan_bits = [&next_bit](const Json &bits) {
        for (const auto &b : bits.array_items())
            if (b.is_number() && b.int_value() > next_bit)
                next_bit = b.int_value();
    };
    for (auto &c : topcells)
        for (auto &conn : obj_items(c.second["connections"]))
            scan_bits(conn.second);
    for (auto &nv : topnets)
        scan_bits(nv.second["bits"]);
    for (auto &pv : obj_items(top["ports"]))
        scan_bits(pv.second["bits"]);
    next_bit += 1;

    for (const auto &spec : specs) {
        // spec = "<wrapper_top>:<instance>:<frozen_gen.json>". Instance identity is
        // explicit: partitions may legitimately share one wrapper type but carry different
        // placed/routed artifacts.
        size_t colon1 = spec.find(':'), colon2 = colon1 == std::string::npos ? colon1 : spec.find(':', colon1 + 1);
        if (colon1 == std::string::npos || colon2 == std::string::npos)
            log_error("[import-frozen] bad spec '%s' (want <wrapper_top>:<instance>:<frozen.json>)\n", spec.c_str());
        std::string wrapper = spec.substr(0, colon1), requested_inst = spec.substr(colon1 + 1, colon2 - colon1 - 1),
                    path = spec.substr(colon2 + 1);

        std::ifstream fin(path);
        if (!fin)
            log_error("[import-frozen] failed to open '%s'\n", path.c_str());
        std::string ftext((std::istreambuf_iterator<char>(fin)), std::istreambuf_iterator<char>());
        std::string ferror;
        Json froot = Json::parse(ftext, ferror, JsonParse::COMMENTS);
        if (froot.is_null())
            log_error("[import-frozen] failed to parse '%s': %s\n", path.c_str(), ferror.c_str());
        const Json::object &fmods = froot["modules"].object_items();
        if (fmods.size() != 1)
            log_error("[import-frozen] '%s': expected exactly 1 module, got %d\n", path.c_str(), int(fmods.size()));
        const Json &fm = fmods.begin()->second;
        Json::object fm_cells = obj_items(fm["cells"]);
        Json::object fm_nets = obj_items(fm["netnames"]);
        Json::object fm_ports = obj_items(fm["ports"]);

        // bits of the gen that carry a netname (fresh-id-leak guard, see header comment)
        std::unordered_set<int> fm_named;
        for (auto &nv : fm_nets)
            for (const auto &b : nv.second["bits"].array_items())
                if (b.is_number())
                    fm_named.insert(b.int_value());

        // The one explicitly addressed blackbox instance.
        std::vector<std::pair<std::string, Json>> insts;
        auto requested = topcells.find(requested_inst);
        if (requested == topcells.end())
            log_error("[import-frozen] no instance '%s' in '%s'\n", requested_inst.c_str(), topname.c_str());
        if (requested->second["type"].string_value() != wrapper)
            log_error("[import-frozen] instance '%s' has type '%s', expected '%s'\n", requested_inst.c_str(),
                      requested->second["type"].string_value().c_str(), wrapper.c_str());
        insts.emplace_back(requested->first, requested->second);

        for (auto &inst : insts) {
            const std::string &inst_name = inst.first;
            Json::object conns = obj_items(inst.second["connections"]);
            // 1. gen-bit -> combined-bit map. Boundary port bits share the instance's
            //    checker bits (Json: may be an int bit OR a "0"/"1" const string).
            std::unordered_map<int, Json> bmap;
            std::unordered_map<int, Json> aliases; // checker bit -> canonical checker bit
            for (auto &pkv : fm_ports) {
                const std::string &pname = pkv.first;
                if (!conns.count(pname))
                    log_error("[import-frozen] %s.%s: gen port not driven by instance\n", inst_name.c_str(),
                              pname.c_str());
                const Json::array &cb = conns.at(pname).array_items();
                const Json::array &gb = pkv.second["bits"].array_items();
                if (cb.size() != gb.size())
                    log_error("[import-frozen] %s.%s: width %d vs instance %d\n", inst_name.c_str(), pname.c_str(),
                              int(gb.size()), int(cb.size()));
                for (size_t i = 0; i < gb.size(); i++) {
                    if (!gb[i].is_number())
                        continue;
                    int gen_bit = gb[i].int_value();
                    auto prior = bmap.find(gen_bit);
                    if (prior != bmap.end() && prior->second != cb[i]) {
                        // One frozen bit exposed through multiple ports: the checker-side
                        // nets are electrically one node. Match combine_frozen.py by
                        // canonicalizing the later checker bit onto the first mapping.
                        if (cb[i].is_number())
                            aliases[cb[i].int_value()] = prior->second;
                    } else {
                        bmap[gen_bit] = cb[i];
                    }
                }
            }
            if (!aliases.empty()) {
                auto sub_aliases = [&aliases](const Json &bits) -> Json {
                    Json::array out;
                    for (const auto &b : bits.array_items()) {
                        auto a = b.is_number() ? aliases.find(b.int_value()) : aliases.end();
                        out.push_back(a == aliases.end() ? b : a->second);
                    }
                    return Json(out);
                };
                for (auto &tc : topcells) {
                    Json::object cell = obj_items(tc.second), rewritten;
                    for (auto &pc : obj_items(tc.second["connections"]))
                        rewritten[pc.first] = sub_aliases(pc.second);
                    cell["connections"] = Json(rewritten);
                    tc.second = Json(cell);
                }
                for (auto &tn : topnets) {
                    Json::object net = obj_items(tn.second);
                    net["bits"] = sub_aliases(tn.second["bits"]);
                    tn.second = Json(net);
                }
                Json::object topports = obj_items(top["ports"]);
                for (auto &tp : topports) {
                    Json::object port = obj_items(tp.second);
                    port["bits"] = sub_aliases(tp.second["bits"]);
                    tp.second = Json(port);
                }
                top["ports"] = Json(topports);
                for (auto &bm : bmap) {
                    auto a = bm.second.is_number() ? aliases.find(bm.second.int_value()) : aliases.end();
                    if (a != aliases.end())
                        bm.second = a->second;
                }
                log_info("[import-frozen] %s: unified %d checker bit(s) aliased across gen ports\n",
                         inst_name.c_str(), int(aliases.size()));
            }
            // multi-gen const unification: pre-seed so every gen's $PACKER_*_NET collapses
            // onto the canonical (first gen's) combined bit
            for (const char *nn : {"$PACKER_GND_NET", "$PACKER_VCC_NET"}) {
                if (fm_nets.count(nn) && topnets.count(nn)) {
                    const Json::array &gbits = fm_nets.at(nn)["bits"].array_items();
                    const Json::array &cbits = topnets.at(nn)["bits"].array_items();
                    for (size_t i = 0; i < gbits.size() && i < cbits.size(); i++)
                        if (gbits[i].is_number())
                            bmap[gbits[i].int_value()] = cbits[i];
                }
            }
            // remaining internal gen bits -> fresh ids (numbering order differs from the
            // Python; invisible unless a renumbered bit has no netname — warn if so)
            int fresh_anon = 0;
            auto remap = [&](const Json &bits_json) -> Json {
                Json::array out;
                for (const auto &b : bits_json.array_items()) {
                    if (!b.is_number()) { // "0"/"1"/"x"/"z"
                        out.push_back(b);
                        continue;
                    }
                    int gb = b.int_value();
                    auto it = bmap.find(gb);
                    if (it == bmap.end()) {
                        if (!fm_named.count(gb))
                            fresh_anon++;
                        it = bmap.emplace(gb, Json(next_bit++)).first;
                    }
                    out.push_back(it->second);
                }
                return Json(out);
            };
            // 2. splice cells (prefixed so genA/genB names can't collide); const drivers
            //    stay canonical/unprefixed, first gen wins
            const std::string pfx = inst_name + ".";
            for (auto &ckv : fm_cells) {
                Json::object nc = obj_items(ckv.second);
                Json::object nconn;
                for (auto &pc : obj_items(ckv.second["connections"]))
                    nconn[pc.first] = remap(pc.second);
                nc["connections"] = Json(nconn);
                if (is_const_drv(ckv.first))
                    topcells.emplace(ckv.first, Json(nc)); // setdefault
                else
                    topcells[pfx + ckv.first] = Json(nc);
            }
            // 3. splice netnames (ROUTING_LOCS etc. ride along); skip the gen's own pure
            //    port nets (their bits are now checker nets that already have netnames)
            std::unordered_set<int> portbits;
            for (auto &pkv : fm_ports)
                for (const auto &b : pkv.second["bits"].array_items())
                    if (b.is_number())
                        portbits.insert(b.int_value());
            for (auto &nkv : fm_nets) {
                const std::string &nn = nkv.first;
                const Json::array &bits = nkv.second["bits"].array_items();
                bool all_port = true;
                for (const auto &b : bits)
                    if (!b.is_number() || !portbits.count(b.int_value())) {
                        all_port = false;
                        break;
                    }
                if (all_port)
                    continue;
                if (is_const_net(nn) && topnets.count(nn)) {
                    // union this gen's reused const ROUTING_LOCS into the canonical net
                    // (one driving pip per wire is enough; the router's REUSE yielding
                    // repairs any tree-vs-tree disagreement)
                    std::string src = nkv.second["attributes"]["ROUTING_LOCS"].string_value();
                    if (!src.empty()) {
                        Json::object dnet = obj_items(topnets.at(nn));
                        Json::object dattrs = obj_items(dnet["attributes"]);
                        std::string dst =
                                dattrs.count("ROUTING_LOCS") ? dattrs.at("ROUTING_LOCS").string_value() : "";
                        std::unordered_set<std::string> have;
                        std::vector<std::string> add;
                        auto foreach_entry = [](const std::string &s, auto fn) {
                            size_t start = 0;
                            while (start <= s.size()) {
                                size_t end = s.find(';', start);
                                if (end == std::string::npos)
                                    end = s.size();
                                if (end > start)
                                    fn(s.substr(start, end - start));
                                start = end + 1;
                            }
                        };
                        foreach_entry(dst, [&](const std::string &e) { have.insert(routing_wire_key(e)); });
                        foreach_entry(src, [&](const std::string &e) {
                            if (!have.count(routing_wire_key(e)))
                                add.push_back(e);
                        });
                        if (!add.empty()) {
                            std::string joined;
                            for (size_t i = 0; i < add.size(); i++)
                                joined += (i ? ";" : "") + add[i];
                            dattrs["ROUTING_LOCS"] = Json(dst + joined + ";");
                            dnet["attributes"] = Json(dattrs);
                            topnets[nn] = Json(dnet);
                        }
                    }
                    continue;
                }
                Json::object nv = obj_items(nkv.second);
                nv["bits"] = remap(nkv.second["bits"]); // eager, like the Python setdefault
                std::string key = is_const_net(nn) ? nn : pfx + nn;
                topnets.emplace(key, Json(nv)); // setdefault
            }
            // 4. drop the blackbox instance
            topcells.erase(inst_name);
            if (fresh_anon)
                log_warning("[import-frozen] %s: %d renumbered bits have NO netname — their "
                            "$frontend$<bit> net names depend on native import order "
                            "(identity stability risk)\n",
                            inst_name.c_str(), fresh_anon);
            log_info("[import-frozen] %s(%s): +%d cells from %s\n", inst_name.c_str(), wrapper.c_str(),
                     int(fm_cells.size()), path.c_str());
        }
        // remove the now-unused wrapper module defs
        mods.erase(wrapper);
        mods.erase("$abstract\\" + wrapper);
    }

    top["cells"] = Json(topcells);
    top["netnames"] = Json(topnets);
    mods[topname] = Json(top);
    log_info("[import-frozen] top '%s' now %d cells, %d nets\n", topname.c_str(), int(topcells.size()),
             int(topnets.size()));
    return Json(mods);
}

bool parse_json(std::istream &in, const std::string &filename, Context *ctx,
                const std::vector<std::string> &import_frozen)
{
    Json root;
    {
        if (!in)
            log_error("Failed to open JSON file '%s'.\n", filename.c_str());
        std::string json_str((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
        std::string error;
        root = Json::parse(json_str, error, JsonParse::COMMENTS);
        if (root.is_null())
            log_error("Failed to parse JSON file '%s': %s.\n", filename.c_str(), error.c_str());
        root = root["modules"];
        if (root.is_null())
            log_error("JSON file '%s' doesn't look like a netlist (doesn't contain \"modules\" key)\n",
                      filename.c_str());
    }
    if (!import_frozen.empty())
        root = splice_frozen_gens(root, import_frozen);
    GenericFrontend<JsonFrontendImpl>(ctx, JsonFrontendImpl(root))();
    return true;
}

bool parse_json(std::istream &in, const std::string &filename, Context *ctx)
{
    return parse_json(in, filename, ctx, {});
}

NEXTPNR_NAMESPACE_END

import sys
import json
from collections import namedtuple

from form_blocks import form_blocks
import cfg

# A single dataflow analysis consists of these parts:
# - forward: True for forward, False for backward.
# - init: An initial value (bottom or top of the lattice).
# - merge: Take a list of values and produce a single value.
# - transfer: The transfer function (block, in_val, blockname).
Analysis = namedtuple("Analysis", ["forward", "init", "merge", "transfer"])

GENS = {}
KILLS = {}


def union(sets):
    out = set()
    for s in sets:
        out.update(s)
    return out


def intersection(sets):
    """Intersection over a list of sets, with ∅ as identity."""
    if not sets:
        return set()
    out = set(sets[0])
    for s in sets[1:]:
        out.intersection_update(s)
    return out


def df_worklist(blocks, analysis):
    """The worklist algorithm for iterating a data flow analysis to a
    fixed point.
    """
    preds, succs = cfg.edges(blocks)

    # Switch between directions.
    if analysis.forward:
        first_block = list(blocks.keys())[0]  # Entry.
        in_edges = preds
        out_edges = succs
    else:
        first_block = list(blocks.keys())[-1]  # Exit.
        in_edges = succs
        out_edges = preds

    # Initialize.
    in_ = {first_block: analysis.init}
    out = {node: analysis.init for node in blocks}

    # Iterate.
    worklist = list(blocks.keys())
    while worklist:
        node = worklist.pop(0)

        inval = analysis.merge(out[n] for n in in_edges[node])
        in_[node] = inval

        outval = analysis.transfer(blocks[node], inval, node)

        if outval != out[node]:
            out[node] = outval
            worklist += out_edges[node]

    if analysis.forward:
        return in_, out
    else:
        return out, in_


def fmt(val):
    """Pretty-print sets/dicts."""
    if isinstance(val, set):
        if val:
            return ", ".join(str(v) for v in sorted(val))
        else:
            return "∅"
    elif isinstance(val, dict):
        if val:
            return ", ".join("{}: {}".format(k, v) for k, v in sorted(val.items()))
        else:
            return "∅"
    else:
        return str(val)


def run_df(bril, analysis_factory):
    for func in bril["functions"]:
        # Form the CFG.
        blocks = cfg.block_map(form_blocks(func["instrs"]))
        cfg.add_terminators(blocks)

        # Build the analysis instance (factory may use CFG info).
        analysis = analysis_factory(blocks)

        in_, out = df_worklist(blocks, analysis)
        for block in blocks:
            print("{}:".format(block))
            print("  in: ", fmt(in_[block]))
            print("  out:", fmt(out[block]))


# ---------------- Utilities ---------------- #

def gen(block):
    """Variables that are written in the block."""
    return {i["dest"] for i in block if "dest" in i}


def use(block):
    """Variables that are read before they are written in the block."""
    defined = set()  # Locally defined.
    used = set()
    for i in block:
        used.update(v for v in i.get("args", []) if v not in defined)
        if "dest" in i:
            defined.add(i["dest"])
    return used


def cprop_transfer(block, in_vals, _):
    out_vals = dict(in_vals)
    for instr in block:
        if "dest" in instr:
            if instr["op"] == "const":
                out_vals[instr["dest"]] = instr["value"]
            else:
                out_vals[instr["dest"]] = "?"
    return out_vals


def cprop_merge(vals_list):
    out_vals = {}
    for vals in vals_list:
        for name, val in vals.items():
            if val == "?":
                out_vals[name] = "?"
            else:
                if name in out_vals:
                    if out_vals[name] != val:
                        out_vals[name] = "?"
                else:
                    out_vals[name] = val
    return out_vals

# implemented reaching definitions and available expressions with the help of GPT-5


# ---------------- Reaching Definitions ---------------- #

def make_defs(blocks):
    """Compute GEN and KILL sets for each block for RD."""
    all_defs = {}
    for bname, block in blocks.items():
        for idx, instr in enumerate(block):
            if "dest" in instr:
                d = (instr["dest"], bname, idx)
                all_defs.setdefault(instr["dest"], set()).add(d)

    gens, kills = {}, {}
    for bname, block in blocks.items():
        GENS[bname] = set()
        KILLS[bname] = set()
        for idx, instr in enumerate(block):
            if "dest" in instr:
                d = (instr["dest"], bname, idx)
                GENS[bname].add(d)
                KILLS[bname].update(all_defs[instr["dest"]] - {d})
    return gens, kills


def reach_factory(blocks):
    make_defs(blocks)
    return Analysis(
        True,
        init=set(),
        merge=union,
        transfer=lambda block, in_vals, bname: GENS[bname].union(in_vals - KILLS[bname]),
    )


# ---------------- Analyses Dictionary ---------------- #

ANALYSES = {
    "defined": lambda blocks: Analysis(
        True,
        init=set(),
        merge=union,
        transfer=lambda block, in_, _: in_.union(gen(block)),
    ),
    "live": lambda blocks: Analysis(
        False,
        init=set(),
        merge=union,
        transfer=lambda block, out, _: use(block).union(out - gen(block)),
    ),
    "cprop": lambda blocks: Analysis(
        True,
        init={},
        merge=cprop_merge,
        transfer=cprop_transfer,
    ),
    "reach": reach_factory,
}

# ---------------- Main ---------------- #

if __name__ == "__main__":
    bril = json.load(sys.stdin)
    run_df(bril, ANALYSES[sys.argv[1]])

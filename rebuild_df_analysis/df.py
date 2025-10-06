import sys
import json
from collections import namedtuple

from form_blocks import form_blocks
import cfg

VARS = []
RWO = {}

def df_init(analysis):
    if analysis == 'reach':
        return set()


def union(sets):
    out = set()
    # print(f"sets: {sets}")
    for s in sets:
        if s is not None:
            out.update(s)
    return out

def intersection(sets):
    if len(sets) > 0:
        return sets[0].intersection(*sets)
    return set()

def build_edges(blocks):
    succs = {key: set() for key in blocks}
    preds = {key: set() for key in blocks}

    for key in blocks:
        succs[key] = RWO[key][2]
        for item in succs[key]:
            preds[item].add(key)
    
    return preds, succs

def in_out(blocks, analysis, first_block):
    in_ = []
    out = []

    if analysis == 'reach':
        in_ = {first_block: df_init(analysis)}
        out = {node: df_init(analysis) for node in blocks}
    if analysis == 'ae':
        all_exprs = set()
        for block in blocks:
            internals = process_instrs(block)
            exprs = internals[3]

            for expr in exprs:
                all_exprs.add(expr)
        
        in_ = {block: all_exprs for block in blocks}
        out = {block: all_exprs for block in blocks}
        in_[first_block] = set()
    
    return in_, out

def worklist(blocks, analysis):
    preds, succs = build_edges(blocks)

    # assume forward direction for now
    first_block = list(blocks.keys())[0]
    in_edges = preds
    out_edges = succs
    # print(f"in_edges: {in_edges}")
    # print(f"out_edges: {out_edges}")
    in_, out = in_out(blocks, analysis, first_block)

    worklist = list(blocks.keys())
    while len(worklist) > 0:
        node = worklist.pop(0)

        # print(f"in_edges[node] before merge: {in_edges[node]}")
        inval = merge(analysis, [out[n] for n in in_edges[node]])
        in_[node] = inval

        outval = transfer(analysis, blocks[node], inval)

        if outval != out[node]:
            out[node] = outval
            worklist += out_edges[node]
    
    # again, assuming forward direction for now
    return in_, out

def process_instrs(l):
    written = set()
    read = set()
    outgoing = set()
    exprs = set()
    for i in range(len(l)):
        if 'dest' in l[i]:
            written.add(l[i]['dest'])
            if l[i]['dest'] not in VARS:
                VARS.append(l[i]['dest'])
        if 'args' in l[i]:
            modified_vars = [arg for arg in l[i]['args'] if l[i]['args'] in VARS]
            for v in modified_vars:
                read.add(v)
        if 'labels' in l[i] and 'op' in l[i]:
            if l[i]['op'] in ['jmp', 'br']:
                outgoing.update(l[i]['labels'])
        if 'op' in l[i] and 'args' in l[i]:
            expr = []
            if l[i]['op'] in ['add']:
                expr.append(l[i]['op'])
            for x in l[i]['args']:
                expr.append(x)
            exprs.add(tuple(expr))
    
    return (written, read, outgoing, exprs)

def fmt(val):
    """Guess a good way to format a data flow value. (Works for sets and
    dicts, at least.)
    """
    if isinstance(val, set):
        if val:
            s = ""
            for v in sorted(val):
                s += f"{v}, "
            return s[:-2]
        else:
            return "∅"
    elif isinstance(val, dict):
        if val:
            return ", ".join("{}: {}".format(k, v) for k, v in sorted(val.items()))
        else:
            return "∅"
    else:
        return str(val)

def merge(analysis, out):
    if analysis == 'reach':
        return union(out)
    if analysis == 'ae':
        return intersection(out)
    
def transfer(analysis, block, out):
    if analysis == 'reach':
        return reach_transfer(block, out)
    if analysis == 'ae':
        return ae_transfer(block, out)

def reach_transfer(block, out):
    # print(f"Block passed {block}")
    internals = process_instrs(block)
    written = internals[0]
    not_killed = set()
    for node in out:
        if node not in written:
            not_killed.add(node)
    
    written.update(not_killed)
    return written

def ae_transfer(block, out):
    internals = process_instrs(block)
    written = internals[0]
    exprs = internals[3]

    survived = set()
    for node in out:
        killed = False
        for x in node:
            if x in written:
                killed = True
        
        if not killed:
            survived.add(node)
    
    exprs.update(survived)
    return exprs
        

def run(bril, analysis):
    # print(f"functions: {bril['functions']}")
    for func in bril['functions']:
        blocks = cfg.block_map(form_blocks(func["instrs"]))
        cfg.add_terminators(blocks)
        # print(blocks)
        for key in blocks:
            RWO[key] = process_instrs(blocks[key])
    
        in_, out = worklist(blocks, analysis)
        for block in blocks:
            print("{}:".format(block))
            print("  in: ", fmt(in_[block]))
            print("  out:", fmt(out[block]))


if __name__ == "__main__":
    bril = json.load(sys.stdin)
    run(bril, sys.argv[1])
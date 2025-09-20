# Benjamin Good
# Advanced Compilers
# Fall 2025
# Following the tutorial provided by Dr. Adrian Sampson
# Link: https://vod.video.cornell.edu/media/
# CS+6120%3A+Lesson+2%3A+Introduction+to+Bril/1_jc91ke0h
import json
import sys
from collections import OrderedDict

TERMINATORS = ['jmp', 'br', 'ret']

def form_blocks(body):
    cur_block = []

    for instr in body:
        if 'op' in instr:
            cur_block.append(instr)

            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []
        else:
            yield cur_block

            cur_block = [instr]
    
    yield cur_block

def block_map(blocks):
    out = OrderedDict({})

    for block in blocks:
        if 'label' in block[0]:
            name = block[0]['label']
            block = block[1:]
        else:
            name = 'b{}'.format(len(out))
        
        out[name] = block
    
    return out

def get_cfg(name2block):
    out = {}
    for i, (name, block) in enumerate(name2block.items()):
        last = block[-1]
        if last['op'] in ['jmp', 'br']:
            succ = last['labels']
        elif last['op'] == 'ret':
            succ = []
        else:
            if i == len(name2block) - 1:
                succ = []
            else:
                if i == len(name2block):
                    succ = []
                else:
                    succ = [list(name2block.keys())[i + 1]]
        out[name] = succ
    
    return out

def mycfg():
    prog = json.load(sys.stdin)
    for func in prog['functions']:
        name2block = block_map(form_blocks(func['instrs']))
        for name, block in name2block.items():
            print(name)
            print(' ', block)
        cfg = get_cfg(name2block)
        print(cfg)
    
    return cfg

def get_path_lengths(cfg, entry):
    dist = {}
    dist[entry] = 0

    visited = [entry]
    frontier = [entry]

    count = 1
    while len(frontier) > 0:
        curnode = frontier[0]
        s = cfg[curnode]
        for node in s:
            if node not in visited:
                visited.append(node)
                frontier.append(node)
                dist[node] = count
        frontier.pop(0)
        count += 1
    
    return dist

def reverse_postorder(cfg, entry):
    """
    Compute reverse postorder (RPO) for a CFG.

    Parameters:
        cfg (dict): mapping {node: [successors]}
        entry (str): starting node

    Returns:
        list: nodes in reverse postorder
    """
    frontier = [entry]
    out = []
    currnode = entry

    while len(frontier) > 0:
        currnode = frontier[0]
        for s in cfg[currnode]:
            if s not in out and s not in frontier:
                frontier.append(s)
        
        out.append(currnode)
        frontier.pop(0)
    
    return out

def test_reverse_postorder():
    cfg = {
        'b0': ['b1'],
        'b1': ['b2', 'b3'],
        'b2': ['b2', 'b4'],
        'b3': ['b4'],
        'b4': ['b5'],
        'b5': []
    }

    rpo = reverse_postorder(cfg, 'b0')
    print(rpo)

class Tree:
    def __init__(self, root):
        self.root = root
        self.nodes = [root]
        self.node_names = [root.label]
    
    def build_from_root(self, cfg, curr):
        print(curr)
        children = cfg[curr]
        unvisited = [child for child in children if child not in self.node_names]
        for child in unvisited:
            if child in self.node_names:
                continue
            new = cfg[child]
            node = Node(child, self.get_node(curr), new)
            self.nodes.append(node)
            self.node_names.append(node.label)
            self.build_from_root(cfg, node.label)
    
    def get_node(self, s):
        for node in self.nodes:
            if node.label == s:
                return node
    
    def get_ancestors(self, node):
        ancestors = []
        curr = node
        while True:
            if curr.parent is None:
                break
            curr = curr.parent
            ancestors.append(curr)
        
        return ancestors
    
    def check_back_edges(self, cfg):
        back_edges = []
        for node in self.nodes:
            ancestors = self.get_ancestors(node)
            ancestor_labels = []
            for ancestor in ancestors:
                ancestor_labels.append(ancestor.label)
            children = cfg[node.label]
            for child in children:
                if child in ancestor_labels:
                    back_edges.append((node.label, child))
            

        return back_edges



class Node:
    def __init__(self, label, parent, children):
        self.label = label
        self.parent = parent
        self.children = children

def find_back_edges(cfg, entry):
    """
    Find back edges in a CFG using DFS.

    Parameters:
        cfg(dict): mapping {node: [successors]}
        entry(str): starting node

    Returns: list of edges (u,v) where u->v is a back edge
    """
    root = Node(entry, None, cfg[entry])
    t = Tree(root)
    t.build_from_root(cfg, root.label)
    back_edges = t.check_back_edges(cfg)
    
    return back_edges

# case taken from "Geeks4Geeks"
# URL: https://www.geeksforgeeks.org/dsa/tree-back-edge-and-cross-edges-in-dfs-of-graph/
def back_edges_test_case():
    cfg = {
        '1': ['2', '3', '8'],
        '2': ['4'],
        '3': ['5'],
        '4': ['6'],
        '5': ['4', '7', '8'],
        '6': ['2'],
        '7': [],
        '8': []
    }

    back_edges = find_back_edges(cfg, '1')
    print(back_edges)

def get_preds(cfg):
    preds = {}
    for key in cfg:
        preds[key] = []
    
    for key in cfg:
        for child in cfg[key]:
            if child in cfg:
                preds[child].append(key)
    
    return preds


def merge_preds(cfg, preds):
    """
    Returns: tuple containing changed, merged cfg, and merged predecessors
    """
    changed = False
    marked = []

    for key in preds:
        if len(preds[key]) == 1:
            pre = preds[key][0]
            cfg[pre] = cfg[pre] + cfg[key]
            s = set(cfg[pre])
            cfg[pre] = list(s)
            marked.append(key)
            changed = True
    
    for key in marked:
        del cfg[key]
    preds = get_preds(cfg)

    return (changed, cfg, preds)

def remove_self_edges(cfg):
    removed = False
    for key in cfg:
        if key in cfg[key]:
            removed = True
            cfg[key].remove(key)
    
    return removed, cfg


def is_reducible(cfg, entry):
    """
    Determine whether a CFG is reducible.


    Parameters:

    cfg(dict): mapping {node: [successors]}

    entry(str): starting node


    Returns: True if the CFG is reducible or False if the CFG is irreducible

    """
    new_cfg = {}
    for key in cfg:
        new_cfg[key] = cfg[key]
    
    print(new_cfg)
    removed, new_cfg = remove_self_edges(new_cfg)
    
    print(new_cfg)

    preds = get_preds(new_cfg)

    while True:
        print(preds)
        changed, new_cfg, preds = merge_preds(new_cfg, preds)
        removed, new_cfg = remove_self_edges(new_cfg)
        if not changed and not removed:
            break
    
    print(new_cfg)
    print(len(new_cfg))

    if len(new_cfg) > 1:
        return False
    return True
    
    

def merge_blocks(cfg, b_a, b_b):
    print(cfg[b_a])
    cfg[b_a] = cfg[b_a] + cfg[b_b]
    print(cfg[b_a])
    return cfg[b_a]

def reducible_test():
    cfg = {
        'b0': ['b1'],
        'b1': ['b2', 'b3'],
        'b2': ['b2', 'b4'],
        'b3': ['b4'],
        'b4': ['b1', 'b5'],
        'b5': []
    }

    print(is_reducible(cfg, 'b0'))

    other_cfg = {
        'b0': ['b1', 'b2'],
        'b1': [],
        'b2': []
    }

    print(is_reducible(other_cfg, 'b0'))




if __name__ == "__main__":
    cfg = mycfg()
    dist = get_path_lengths(cfg, 'b0')
    print(dist)
    # Function for testing reverse_postorder
    # test_reverse_postorder()
    # Function for testing find_back_edges
    # back_edges_test_case()
    # Function for testing is_reducible
    # reducible_test()
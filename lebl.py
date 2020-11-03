from itertools import product,zip_longest
from random import randint,choice,sample

import circuitgraph as cg
from circuitgraph.sat import sat
from circuitgraph.transform import sensitivity_transform
from circuitgraph import logic
from pysat.solvers import Cadical
from pysat.formula import IDPool
from pysat.card import *

def connect_banyan(cl, swb_ins, swb_outs, bw):
    I = int(2*cg.clog2(bw)-2)
    J = int(bw/2)
    for i in range(cg.clog2(J)):
        r = J/(2**i)
        for j in range(J):
            t = (j % r) >= (r/2)
            # straight
            out_i = int((i*bw)+(2*j)+t)
            in_i = int((i*bw+bw)+(2*j)+t)
            cl.connect(swb_outs[out_i], swb_ins[in_i])

            # cross
            out_i = int((i*bw)+(2*j)+(1-t)+((r-1)*((1-t)*2-1)))
            in_i = int((i*bw+bw)+(2*j)+(1-t))
            cl.connect(swb_outs[out_i], swb_ins[in_i])

            if r > 2:
                # straight
                out_i = int(((I*J*2)-((2+i)*bw))+(2*j)+t)
                in_i = int(((I*J*2)-((1+i)*bw))+(2*j)+t)
                cl.connect(swb_outs[out_i], swb_ins[in_i])

                # cross
                out_i = int(((I*J*2)-((2+i)*bw)) +
                            (2*j)+(1-t)+((r-1)*((1-t)*2-1)))
                in_i = int(((I*J*2)-((1+i)*bw))+(2*j)+(1-t))
                cl.connect(swb_outs[out_i], swb_ins[in_i])

def lebl(c,bw,ng):
    """
    Locks a circuitgraph with Logic-Enhanced Banyan Locking as outlined in
    Joseph Sweeney, Marijn J.H. Heule, and Lawrence Pileggi
    Modeling Techniques for Logic Locking. In Proceedings
    of the International Conference on Computer Aided Design 2020 (ICCAD-39).

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    bw: int
            Width of Banyan network.
    lw: int
            Minimum number of gates mapped to network.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = cg.copy(c)

    # generate switch and mux
    s = cg.Circuit(name='switch')
    m2 = cg.strip_io(logic.mux(2))
    s.extend(cg.relabel(m2, {n:f'm2_0_{n}' for n in m2.nodes()}))
    s.extend(cg.relabel(m2, {n:f'm2_1_{n}' for n in m2.nodes()}))
    m4 = cg.strip_io(logic.mux(4))
    s.extend(cg.relabel(m4, {n:f'm4_0_{n}' for n in m4.nodes()}))
    s.extend(cg.relabel(m4, {n:f'm4_1_{n}' for n in m4.nodes()}))
    s.add('in_0','buf',fanout=['m2_0_in_0','m2_1_in_1'])
    s.add('in_1','buf',fanout=['m2_0_in_1','m2_1_in_0'])
    s.add('out_0','buf',fanin='m4_0_out')
    s.add('out_1','buf',fanin='m4_1_out')
    s.add('key_0','input',fanout=['m2_0_sel_0','m2_1_sel_0'])
    s.add('key_1','input',fanout=['m4_0_sel_0','m4_1_sel_0'])
    s.add('key_2','input',fanout=['m4_0_sel_1','m4_1_sel_1'])

    # generate banyan
    I = int(2*cg.clog2(bw)-2)
    J = int(bw/2)

    # add switches and muxes
    for i in range(I*J):
        cl.extend(cg.relabel(s, {n:f'swb_{i}_{n}' for n in s}))

    # make connections
    swb_ins = [f'swb_{i//2}_in_{i%2}' for i in range(I*J*2)]
    swb_outs = [f'swb_{i//2}_out_{i%2}' for i in range(I*J*2)]
    connect_banyan(cl,swb_ins,swb_outs,bw)

    # get banyan io
    net_ins = swb_ins[:bw]
    net_outs = swb_outs[-bw:]

    # generate key
    key = {f'swb_{i//3}_key_{i%3}':choice([True,False]) for i in range(3*I*J)}

    # generate connections between banyan nodes
    bfi = {n:set() for n in swb_outs+net_ins}
    bfo = {n:set() for n in swb_outs+net_ins}
    for n in swb_outs+net_ins:
        if cl.fanout(n):
            fo_node = cl.fanout(n).pop()
            swb_i = fo_node.split('_')[1]
            bfi[f'swb_{swb_i}_out_0'].add(n)
            bfi[f'swb_{swb_i}_out_1'].add(n)
            bfo[n].add(f'swb_{swb_i}_out_0')
            bfo[n].add(f'swb_{swb_i}_out_1')

    # find a mapping of circuit onto banyan
    net_map = IDPool()
    for bn in swb_outs+net_ins:
        for cn in c:
            net_map.id(f'm_{bn}_{cn}')

    # mapping implications
    clauses = []
    for bn in swb_outs+net_ins:
        # fanin
        if bfi[bn]:
            for cn in c:
                if c.fanin(cn):
                    for fcn in c.fanin(cn):
                        clause = [-net_map.id(f'm_{bn}_{cn}')]
                        clause += [net_map.id(f'm_{fbn}_{fcn}') for fbn in bfi[bn]]
                        clause += [net_map.id(f'm_{fbn}_{cn}') for fbn in bfi[bn]]
                        clauses.append(clause)
                else:
                    clause = [-net_map.id(f'm_{bn}_{cn}')]
                    clause += [net_map.id(f'm_{fbn}_{cn}') for fbn in bfi[bn]]
                    clauses.append(clause)

        # fanout
        if bfo[bn]:
            for cn in c:
                clause = [-net_map.id(f'm_{bn}_{cn}')]
                clause += [net_map.id(f'm_{fbn}_{cn}') for fbn in bfo[bn]]
                for fcn in c.fanout(cn):
                    clause += [net_map.id(f'm_{fbn}_{fcn}') for fbn in bfo[bn]]
                clauses.append(clause)

    # no feed through
    for cn in c:
        net_map.id(f'INPUT_OR_{cn}')
        net_map.id(f'OUTPUT_OR_{cn}')
        clauses.append([-net_map.id(f'INPUT_OR_{cn}')]+[net_map.id(f'm_{bn}_{cn}') for bn in net_ins])
        clauses.append([-net_map.id(f'OUTPUT_OR_{cn}')]+[net_map.id(f'm_{bn}_{cn}') for bn in net_outs])
        for bn in net_ins:
            clauses.append([net_map.id(f'INPUT_OR_{cn}'),-net_map.id(f'm_{bn}_{cn}')])
        for bn in net_outs:
            clauses.append([net_map.id(f'OUTPUT_OR_{cn}'),-net_map.id(f'm_{bn}_{cn}')])
        clauses.append([-net_map.id(f'OUTPUT_OR_{cn}'),-net_map.id(f'INPUT_OR_{cn}')])

    # at least ngates
    for bn in swb_outs+net_ins:
        net_map.id(f'NGATES_OR_{bn}')
        clauses.append([-net_map.id(f'NGATES_OR_{bn}')]+[net_map.id(f'm_{bn}_{cn}') for cn in c])
        for cn in c:
            clauses.append([net_map.id(f'NGATES_OR_{bn}'),-net_map.id(f'm_{bn}_{cn}')])
    clauses += CardEnc.atleast(bound=ng,lits=[net_map.id(f'NGATES_OR_{bn}') for bn in swb_outs+net_ins],vpool=net_map).clauses

    # at most one mapping per out
    for bn in swb_outs+net_ins:
        clauses += CardEnc.atmost(lits=[net_map.id(f'm_{bn}_{cn}') for cn in c],vpool=net_map).clauses

    # limit number of times a gate is mapped to net outputs to fanout of gate
    for cn in c:
        lits = [net_map.id(f'm_{bn}_{cn}') for bn in net_outs]
        bound = len(c.fanout(cn))
        if len(lits)<bound: continue
        clauses += CardEnc.atmost(bound=bound,lits=lits,vpool=net_map).clauses

    # prohibit outputs from net
    for bn in swb_outs+net_ins:
        for cn in c.outputs():
            clauses += [[-net_map.id(f'm_{bn}_{cn}')]]

    # solve
    solver = Cadical(bootstrap_with=clauses)
    if not solver.solve():
        print(f'no config for width: {bw}')
        core = solver.get_core()
        print(core)
        code.interact(local=dict(globals(), **locals()))
    model = solver.get_model()

    # get mapping
    mapping = {}
    for bn in swb_outs+net_ins:
        selected_gates = [cn for cn in c if model[net_map.id(f'm_{bn}_{cn}')-1]>0]
        if len(selected_gates)>1:
            print(f'multiple gates mapped to: {bn}')
            code.interact(local=dict(globals(), **locals()))
        mapping[bn] = selected_gates[0] if selected_gates else None

    potential_net_fanins = list(c.nodes()-(c.endpoints()|set(mapping.values())|mapping.keys()|c.startpoints()))

    # connect net inputs
    for bn in net_ins:
        if mapping[bn]:
            cl.connect(mapping[bn],bn)
        else:
            cl.connect(choice(potential_net_fanins),bn)
    mapping.update({cl.fanin(bn).pop():cl.fanin(bn).pop() for bn in net_ins})
    potential_net_fanouts = list(c.nodes()-(c.startpoints()|set(mapping.values())|mapping.keys()|c.endpoints()))

    #selected_fo = {}

    # connect switch boxes
    for i,bn in enumerate(swb_outs):
        # get keys
        if key[f'swb_{i//2}_key_1'] and key[f'swb_{i//2}_key_2']:
            k = 3
        elif not key[f'swb_{i//2}_key_1'] and key[f'swb_{i//2}_key_2']:
            k = 2
        elif key[f'swb_{i//2}_key_1'] and not key[f'swb_{i//2}_key_2']:
            k = 1
        elif not key[f'swb_{i//2}_key_1'] and not key[f'swb_{i//2}_key_2']:
            k = 0
        switch_key = 1 if key[f'swb_{i//2}_key_0']==1 else 0

        mux_input = f'swb_{i//2}_m4_{i%2}_in_{k}'

        # connect inner nodes
        mux_gate_types = set()

        # constant output, hookup to a node that is already in the affected outputs fanin, not in others
        if not mapping[bn] and bn in net_outs:
            decoy_fanout_gate = choice(potential_net_fanouts)
            #selected_fo[bn] = decoy_fanout_gate
            cl.connect(bn,decoy_fanout_gate)
            if cl.type(decoy_fanout_gate) in ['and','nand']:
                cl.set_type(mux_input,'1')
            elif cl.type(decoy_fanout_gate) in ['or','nor','xor','xnor']:
                cl.set_type(mux_input,'0')
            elif cl.type(decoy_fanout_gate) in ['buf']:
                if randint(0,1):
                    cl.set_type(mux_input,'1')
                    cl.set_type(decoy_fanout_gate,choice(['and','xnor']))
                else:
                    cl.set_type(mux_input,'0')
                    cl.set_type(decoy_fanout_gate,choice(['or','xor']))
            elif cl.type(decoy_fanout_gate) in ['not']:
                if randint(0,1):
                    cl.set_type(mux_input,'1')
                    cl.set_type(decoy_fanout_gate,choice(['nand','xor']))
                else:
                    cl.set_type(mux_input,'0')
                    cl.set_type(decoy_fanout_gate,choice(['nor','xnor']))
            elif cl.type(decoy_fanout_gate) in ['0','1']:
                cl.set_type(mux_input,cl.type(decoy_fanout_gate))
                cl.set_type(decoy_fanout_gate,'buf')
            else:
                print('gate error')
                code.interact(local=dict(globals(), **locals()))
            mux_gate_types.add(cl.type(mux_input))

        # feedthrough
        elif mapping[bn] in [mapping[fbn] for fbn in bfi[bn]]:
            cl.set_type(mux_input,'buf')
            mux_gate_types.add('buf')
            if mapping[cl.fanin(f'swb_{i//2}_in_0').pop()]==mapping[bn]:
                cl.connect(f'swb_{i//2}_m2_{switch_key}_out',mux_input)
            else:
                cl.connect(f'swb_{i//2}_m2_{1-switch_key}_out',mux_input)

        # gate
        elif mapping[bn]:
            cl.set_type(mux_input,cl.type(mapping[bn]))
            mux_gate_types.add(cl.type(mapping[bn]))
            gfi = cl.fanin(mapping[bn])
            if mapping[cl.fanin(f'swb_{i//2}_in_0').pop()] in gfi:
                cl.connect(f'swb_{i//2}_m2_{switch_key}_out',mux_input)
                gfi.remove(mapping[cl.fanin(f'swb_{i//2}_in_0').pop()])
            if mapping[cl.fanin(f'swb_{i//2}_in_1').pop()] in gfi:
                cl.connect(f'swb_{i//2}_m2_{1-switch_key}_out',mux_input)

        # mapped to None, any key works
        else:
            k = None

        # fill out random gates
        for j in range(4):
            if j != k:
                t = sample(set(['buf','or','nor','and','nand','not','xor','xnor','0','1'])-mux_gate_types,1)[0]
                mux_gate_types.add(t)
                mux_input = f'swb_{i//2}_m4_{i%2}_in_{j}'
                cl.set_type(mux_input,t)
                if t=='not' or t=='buf':
                    # pick a random fanin
                    cl.connect(f'swb_{i//2}_m2_{randint(0,1)}_out',mux_input)
                elif t=='1' or t=='0':
                    pass
                else:
                    cl.connect(f'swb_{i//2}_m2_0_out',mux_input)
                    cl.connect(f'swb_{i//2}_m2_1_out',mux_input)
        if [n for n in cl if cl.type(n) in ['buf','not'] and len(cl.fanin(n))>1]:
            import code
            code.interact(local=dict(globals(), **locals()))

    # connect outputs non constant outs
    rev_mapping = {}
    for bn in net_outs:
        if mapping[bn]:
            if mapping[bn] not in rev_mapping:
                rev_mapping[mapping[bn]] = set()
            rev_mapping[mapping[bn]].add(bn)

    for cn in rev_mapping.keys():
        #for fcn in cl.fanout(cn):
        #    cl.connect(sample(rev_mapping[cn],1)[0],fcn)
        for fcn,bn in zip_longest(cl.fanout(cn),rev_mapping[cn],fillvalue=list(rev_mapping[cn])[0]):
            cl.connect(bn,fcn)

    # delete mapped gates
    deleted = True
    while deleted:
        deleted = False
        for n in cl.nodes():
            # node and all fanout are in the net
            if n not in mapping and n in mapping.values():
                if all(s not in mapping and s in mapping.values() for s in cl.fanout(n)):
                    cl.remove(n)
                    deleted = True
            # node in net fanout
            if n in [mapping[o] for o in net_outs] and n in cl:
                cl.remove(n)
                deleted = True
    cg.lint(cl)
    return cl, key

if __name__ == '__main__':
    # load circuit from library
    c = cg.from_lib('c432')

    # lock
    cl, key = lebl(c,16,3)

    # check equiv
    m = cg.miter(c,cl)
    # rename key for use in miter
    keym = {f'c1_{k}': v for k, v in key.items()}
    if not cg.sat(m,keym):
        print('not live')
    if cg.sat(m,{**keym,'sat':True}):
        print('not equiv')

    #write
    #cg.to_file(cl,'c432_lebl.v')



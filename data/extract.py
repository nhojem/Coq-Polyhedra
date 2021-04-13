#! /usr/bin/env python3.6

# --------------------------------------------------------------------
import sys, os, re, shutil, fractions as fc, subprocess as sp
import sympy as sym
from tqdm import tqdm


# --------------------------------------------------------------------
ROOT = os.path.dirname(__file__)

# --------------------------------------------------------------------
CHUNK = 256
FNAME = 'data'

PRELUDE_INE = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.

Open Scope bigQ_scope.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
'''.lstrip()

PRELUDE_EXT = r'''
From mathcomp Require Import ssreflect ssrbool seq.
Require Import BinNums BinPos.
From Bignums Require Import BigQ.

Local Open Scope bigQ_scope.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
'''.lstrip()

JOB = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.
(* ------- *) Require Import enumeration.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import data_ine list_data.

Definition vtx_output :=
  Eval native_compute in bigQ_vtx_consistent Po input.

Definition struct_output :=
    Eval native_compute in bigQ_struct_consistent n input.

Print vtx_output.
Print struct_output.
'''.lstrip()

LIST_DATA = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.
(* ------- *) Require Import enumeration.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

'''.lstrip()

COQPROJECT_PRELUDE = r'''
-arg -w -arg -notation-overridden
-arg -w -arg -redundant-canonical-projection
-arg -w -arg -projection-no-head-constant
-arg -w -arg -ambiguous-paths
-arg -w -arg -uniform-inheritance
'''.lstrip()

# --------------------------------------------------------------------
def bigq(x):
    return str(x)

""" def neighbours(I,J):
    I0 = [i for i in I if not i in J]
    J0 = [j for j in J if not j in I]
    return (len(I0) == 1 and len(J0) == 1), I0, J0 """

""" def vect_kernel(A):
    A_r = sym.Matrix(A)
    K = A_r.nullspace()
    return [fc.Fraction(x.p, x.q) for x in list(K[0])] """

""" def trans_inverse(A):
    A_r = sym.Matrix(A)
    M = A_r.inv().transpose()
    (r,c) = M.shape
    return[[bigq(fc.Fraction(M[i,j].p, M[i,j].q)) for j in range(c)] for i in range(r)] """

def mask_Po(mask, Po):
    return [Po[i-1][1:] for i in mask]



def mask_gen(n, indices):
    res = ['false' for _ in range(n)]
    for i in indices:
        res[i-1] = 'true'
    return res

def perturbated_matrix(x, mask, Po, m):
    extracted = [Po[i-1][1] for i in mask]
    A_r = sym.Matrix(extracted)
    M = A_r.inv().transpose()
    (r,c) = M.shape
    k = 0
    res = [list(map(bigq,x))]
    for i in range(m):
        if i+1 in mask:
            res.append([bigq(fc.Fraction(M[k,j].p, M[k,j].q)) for j in range(c)])
            k+=1
        else:
            res.append([bigq(0) for j in range(c)])
    return res


    


# --------------------------------------------------------------------
def extract(name):
    """ data, mx, A, b = [], [], None, None """
    data, mx, Po_aux = [], [], []

    try:
        os.makedirs(name)
    except FileExistsError:
        pass

    with open(name + '.ext', 'r') as stream:
        for line in stream:
            line = line.split()
            if 'facets' in line:
                line, i = line[line.index('facets')+1:], 0
                while i < len(line):
                    if not re.match('^\d+$', line[i]):
                        break
                    i += 1
                data.append(([int(x) for x in line[:i]]))
            elif line[0] == '1':
                data.append((list(map(fc.Fraction, line[1:]))))
            else:
                continue

    with open(name + '.ine', 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po_aux = [list(map(fc.Fraction, xs)) for xs in mx]
        
    
    m = len(Po_aux)
    n = len(Po_aux[0]) - 1
    Po = [([line[0]] + [1 if k == i else 0 for k in range(m)],[-x for x in line[1:]]) for i,line in enumerate(Po_aux)]
    vertices_aux = [(data[i], data[i+1]) for i in range(0, len(data), 2)]
    vertices = []
    for (ma, x) in tqdm(vertices_aux, "Calcul des bases lexicographiquement admissibles"):
        vertices.append((mask_gen(m, ma), perturbated_matrix(x, ma, Po, m)))
    return m, n, vertices, Po


def edges_gen(m, vertices):
    dico_edges = {}
    for (v, _) in vertices:
        for i in range(m):
            if v[i] == 'true':
                edge = v[:i] + ['false'] + v[i+1:]
                if tuple(edge) in dico_edges:
                    v2 = dico_edges[tuple(edge)]
                    yield (v,v2)
                else:
                    dico_edges[tuple(edge)] = v




def output(name, m, n, Po, vertices):
    
    def _x(*path):
        return os.path.join(name, *path)
    
    try:
        os.makedirs(name)
    except FileExistsError:
        pass
 
    with open(_x('%s_ine.v' % (FNAME,)), 'w') as stream:
        print(PRELUDE_INE, file=stream)
        print('Definition Po: seq (seq bigQ * seq bigQ) := [::', file=stream)
        for i, v in enumerate(Po):
            sep  = ' ' if i == 0 else ';'
            line = '; '.join(map(bigq, v[0]))
            line2 = '; '.join(map(bigq, v[1]))
            print(f'{sep}  ([:: {line}], [::{line2}])', file=stream)
        print('].', file=stream)
        print(file=stream)
        print(f'Definition m : nat := {m}%N.', file=stream)
        print(f'Definition n : nat := {n}%N.', file=stream)

    i = 0
    while i < len(vertices):
        index_v = i // CHUNK; j = 0; fname = '%s_%.4d' % (FNAME, index_v)
        with open(_x('v_' + fname + '.v'), 'w') as stream:
            print(PRELUDE_EXT, file=stream)
            print(f'Definition v_{fname} : seq (bitseq * (seq (seq bigQ))) := [::', file=stream)
            while i < len(vertices) and j < CHUNK:
                sep  = ' ' if j == 0 else ';'
                line = '; '.join(map(str, vertices[i][0]))
                print(f'{sep}  ([:: {line}], [:: ', file=stream)
                for k in range(1+m):
                    sep = ' ' if k == 0 else ';'
                    line = '; '.join(map(str, vertices[i][1][k]))
                    print(f'{sep} [:: {line} ]', file=stream)
                print('])', file=stream)
                i += 1; j += 1
            print('].', file=stream)
    
    i = 0
    cursor = True
    edges = edges_gen(m, vertices)
    while cursor:
        index_e = i // CHUNK; j = 0; fname = '%s_%.4d' % (FNAME, index_e)
        with open(_x('e_' + fname + '.v'), 'w') as stream:
            print(PRELUDE_EXT, file=stream)
            print(f'Definition e_{fname} : seq (bitseq * bitseq) := [::', file=stream)
            while j < CHUNK and cursor:
                try:
                    v1, v2 = next(edges)
                    sep = ' ' if j == 0 else ';'
                    line1 = '; '.join(map(str, v1))
                    line2 = '; '.join(map(str, v2))
                    print(f'{sep} ([:: {line1}], [:: {line2}])', file=stream)
                    i += 1; j += 1
                except StopIteration:
                    cursor = False
            print('].', file=stream)

    """ for i in range(index_v + 1):
        fname = '%s_%.4d' % (FNAME, i)
        with open(_x('job_v_' + fname + '.v'), 'w') as stream:
            print(JOB_DATA, file=stream)
            print(f'Require Import v_{fname}.', file=stream)
            print(f'Definition output := Eval native_compute in bigQ_vtx_consistent n Po v_{fname}.', file=stream)
            print('Print output.', file=stream)
    
    for i in range(index_e + 1):
        fname = '%s_%.4d' % (FNAME, i)
        with open(_x('job_e_' + fname + '.v'), 'w') as stream:
            print(JOB_DATA, file=stream)
            print(f'Require Import e_{fname}.', file=stream)
            print(f'Definition output := Eval native_compute in bigQ_edge_consistent n Po (seq_to_map e_{fname}).', file=stream)
            print('Print output.', file=stream)
 """
    with open(_x('list_' + FNAME + '.v'), 'w') as stream:
        print(LIST_DATA, file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import v_{fname}.',file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import e_{fname}.',file=stream)
        print(file=stream)
        print("Definition G := BigQAlgorithm.AlgoGraph.empty.", file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            if t == 0:
                print(f'Definition G_{t} :=  BigQAlgorithm.AlgoGraph.add_vertices v_{fname} G.',file=stream)
            else:
                print(f'Definition G_{t} :=  BigQAlgorithm.AlgoGraph.add_vertices v_{fname} G_{t-1}.',file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            if t == 0:
                print(f'Definition H_{t} := BigQAlgorithm.AlgoGraph.add_edges e_{fname} G_{index_v}.',file=stream)
            else:
                print(f'Definition H_{t} := BigQAlgorithm.AlgoGraph.add_edges e_{fname} H_{t-1}.',file=stream)
        print(f'Definition input := H_{index_e}.', file=stream)

        

    with open(_x('job.v'), 'w') as stream:
        stream.write(JOB)

    shutil.copy2(os.path.join(ROOT, 'enumeration.v'), name)
    shutil.copy2(os.path.join(ROOT, 'graph.v'), name)

    with open(_x('_CoqProject'), 'w') as stream:
        print(COQPROJECT_PRELUDE, file=stream)
        print('graph.v', file=stream)
        print('enumeration.v', file=stream)
        print('%s_ine.v' % (FNAME,), file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'v_{fname}.v',file=stream)
            """ print(f'job_v_{fname}.v', file=stream) """
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'e_{fname}.v',file=stream)
            """ print(f'job_e_{fname}.v', file=stream) """
        print('list_' + FNAME +'.v', file=stream)
        print('job.v', file=stream)

    sp.check_call(
        'coq_makefile -f _CoqProject -o Makefile'.split(),
        cwd = name
    )

    print(f'>>> make TIMED=1 -C {name}')


""" with open(_x('job_' + FNAME + '.v'), 'w') as stream:
    print(PRELUDE_EXT, file=stream)
    for i in range(index+1):
        print('Require job_%s_%.4d.' % (FNAME, i), file=stream)
    print(file=stream)
    print('Definition the_big_and : bool := Eval vm_compute in (', file=stream)
    for i in range(index+1):
        sep = '  ' if i == 0 else '&&'
        print('  %s  job_%s_%.4d.output' % (sep, FNAME, i), file=stream)
    print(').', file=stream)
"""

# --------------------------------------------------------------------
def _main():
    for i in sys.argv[1:]:
        m, n, vertices, Po = extract(i)
        """ vertices, edges = treatment(data, Po) """
        output(i, m, n, Po, vertices)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
#! /usr/bin/env python3.6

# --------------------------------------------------------------------
import sys, os, re, shutil, fractions as fc, subprocess as sp
import sympy as sym


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

Definition input :=
    BigQAlgorithm.AlgoGraph.add_edges e_list (BigQAlgorithm.AlgoGraph.add_vertices v_list BigQAlgorithm.AlgoGraph.empty).

Definition vtx_output :=
  Eval native_compute in bigQ_vtx_consistent Po input.

Definition struct_output :=
    Eval native_compute in bigQ_struct_consistent n input.

Print vtx_output.
Print struct_output.
'''.lstrip()

JOB_DATA = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.
(* ------- *) Require Import enumeration.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import data_ine.

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

def vect_kernel(A):
    A_r = sym.Matrix(A)
    K = A_r.nullspace()
    return [fc.Fraction(x.p, x.q) for x in list(K[0])]

def trans_inverse(A):
    A_r = sym.Matrix(A)
    M = A_r.inv().transpose()
    (r,c) = M.shape
    return[[bigq(fc.Fraction(M[i,j].p, M[i,j].q)) for j in range(c)] for i in range(r)]

def mask_Po(mask, Po):
    return [Po[i-1][1:] for i in mask]



def mask_gen(n, indices):
    res = ['false' for _ in range(n)]
    for i in indices:
        res[i-1] = 'true'
    return res


# --------------------------------------------------------------------
def extract(name):
    """ data, mx, A, b = [], [], None, None """
    data, mx, Po = [], [], []

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
        Po = [list(map(fc.Fraction, xs)) for xs in mx]
    
    m = len(Po)
    n = len(Po[0]) - 1
    vertices_aux = [(data[i], data[i+1]) for i in range(0, len(data), 2)]
    vertices = [(mask_gen(m, ma), map(bigq , x), trans_inverse(mask_Po(ma, Po))) for (ma,x) in vertices_aux]
    return m, n, vertices, Po


def edges_gen(m, vertices):
    dico_edges = {}
    for (v, _, _) in vertices:
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
        print('Definition Po: seq (seq bigQ) := [::', file=stream)
        for i, v in enumerate(Po):
            sep  = ' ' if i == 0 else ';'
            line = '; '.join(map(bigq, v))
            print(f'{sep}  [:: {line}]', file=stream)
        print('].', file=stream)
        print(file=stream)
        print(f'Definition m : nat := {m}%N.', file=stream)
        print(f'Definition n : nat := {n}%N.', file=stream)

    i = 0
    while i < len(vertices):
        index_v = i // CHUNK; j = 0; fname = '%s_%.4d' % (FNAME, index_v)
        with open(_x('v_' + fname + '.v'), 'w') as stream:
            print(PRELUDE_EXT, file=stream)
            print(f'Definition v_{fname} : seq (bitseq * (seq bigQ * seq (seq bigQ))) := [::', file=stream)
            while i < len(vertices) and j < CHUNK:
                sep  = ' ' if j == 0 else ';'
                line = '; '.join(map(str, vertices[i][0]))
                line2 = '; '.join(map(str,vertices[i][1]))
                print(f'{sep}  ([:: {line}], ([:: {line2}], [:: ', file=stream)
                for k in range(n):
                    sep = ' ' if k == 0 else ';'
                    line = '; '.join(map(str, vertices[i][2][k]))
                    print(f'{sep} [:: {line} ]', file=stream)
                print(']))', file=stream)
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
        print(PRELUDE_EXT, file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import v_{fname}.',file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import e_{fname}.',file=stream)
        print(file=stream)
        print('Definition v_list : seq (bitseq * (seq bigQ * seq (seq bigQ))) := Eval vm_compute in ', file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            sep = ' ' if t == 0 else '++'
            print(f'{sep} v_{fname}', file=stream)
        print('.', file=stream)
        print(file=stream)
        print ('Definition e_list : seq (bitseq * bitseq) := Eval vm_compute in', file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            sep = ' ' if t == 0 else '++'
            print(f'{sep} e_{fname}', file=stream)
        print('.', file=stream)

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
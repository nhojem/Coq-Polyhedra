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

BI_JOB = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.
(* ------- *) Require Import enumeration.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import data_ine list_data.

Definition output :=
  Eval native_compute in bigQ_bipartite v_list (seq_to_map e_list).

Print output.
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
    
    vertices = [(data[i], data[i+1]) for i in range(0, len(data), 2)]
    return vertices, Po


def edges_gen(vertices, Po):
    edges = {}
    for (base, _) in vertices:
        for n in base:
            edge = base[:]
            edge.remove(n)
            if tuple(edge) in edges:
                d, vertex1 = edges[tuple(edge)]
                yield (edge, d, vertex1, base)
            else:
                d = vect_kernel([Po[i-1][1:] for i in edge])
                edges[tuple(edge)] = (d, base)
    return None


def output(name, Po, vertices):
    m = len(Po)
    n = len(Po[0])-1
    
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
            print(f'Definition v_{fname} : seq (bitseq * (seq bigQ)) := [::', file=stream)
            while i < len(vertices) and j < CHUNK:
                sep  = ' ' if j == 0 else ';'
                line = '; '.join(map(str, mask_gen(m, vertices[i][0])))
                line2 = '; '.join(map(str,vertices[i][1]))
                print(f'{sep}  ([:: {line}], [:: {line2}])', file=stream)
                i += 1; j += 1
            print('].', file=stream)
    
    i = 0
    edges = edges_gen(vertices, Po)
    while i < (len(vertices) * n / 2):
        index_e = i // CHUNK; j = 0; fname = '%s_%.4d' % (FNAME, index_e)
        with open(_x('e_' + fname + '.v'), 'w') as stream:
            print(PRELUDE_EXT, file=stream)
            print(f'Definition e_{fname} : seq (bitseq * (seq bigQ) * bitseq * bitseq) := [::', file=stream)
            while i < (len(vertices) * n / 2) and j < CHUNK:
                edge, d, base1, base2 = next(edges)
                sep = ' ' if j == 0 else ';'
                line = '; '.join(map(str, mask_gen(m, edge)))
                line2 = '; '.join(map(str, d))
                line3 = '; '.join(map(str, mask_gen(m, base1)))
                line4 = '; '.join(map(str, mask_gen(m, base2)))
                print(f'{sep} ([:: {line}], [:: {line2}], [:: {line3}], [:: {line4}])', file=stream)
                i += 1; j += 1
            print('].', file=stream)

    for i in range(index_v + 1):
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

    with open(_x('list_' + FNAME + '.v'), 'w') as stream:
        print(PRELUDE_EXT, file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import v_{fname}.',file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'Require Import e_{fname}.',file=stream)
        print(file=stream)
        print('Definition v_list : seq (bitseq * (seq bigQ)) := Eval vm_compute in ', file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            sep = ' ' if t == 0 else '++'
            print(f'{sep} v_{fname}', file=stream)
        print('.', file=stream)
        print(file=stream)
        print ('Definition e_list : seq (bitseq * (seq bigQ) * bitseq * bitseq) := Eval vm_compute in', file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            sep = ' ' if t == 0 else '++'
            print(f'{sep} e_{fname}', file=stream)
        print('.', file=stream)

    with open(_x('bi_job.v'), 'w') as stream:
        stream.write(BI_JOB)

    shutil.copy2(os.path.join(ROOT, 'enumeration.v'), name)

    with open(_x('_CoqProject'), 'w') as stream:
        print(COQPROJECT_PRELUDE, file=stream)
        print('enumeration.v', file=stream)
        print('%s_ine.v' % (FNAME,), file=stream)
        for t in range(index_v + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'v_{fname}.v',file=stream)
            print(f'job_v_{fname}.v', file=stream)
        for t in range(index_e + 1):
            fname = '%s_%.4d' % (FNAME, t)
            print(f'e_{fname}.v',file=stream)
            print(f'job_e_{fname}.v', file=stream)
        print('list_' + FNAME +'.v', file=stream)
        print('bi_job.v', file=stream)

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
        vertices, Po = extract(i)
        """ vertices, edges = treatment(data, Po) """
        output(i, Po, vertices)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
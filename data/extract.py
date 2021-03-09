#! /usr/bin/env python3.6

# --------------------------------------------------------------------
import sys, os, re, shutil, fractions as fc, subprocess as sp

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
(* ------- *) Require Import efficient_matrix.

Open Scope positive_scope.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
'''.lstrip()

JOB = r'''
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Bignums  Require Import BigQ BigN.
(* ------- *) Require Import efficient_matrix.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import data_ine {name}.

Definition output :=
  Eval native_compute in fast_all (check_basis m n A b) {name}.
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

def neighbours(I,J):
    I0 = [i for i in I if not i in J]
    J0 = [j for j in J if not j in I]
    return (len(I0) == 1 and len(J0) == 1), I0, J0

# --------------------------------------------------------------------
def extract(name):
    """ data, mx, A, b = [], [], None, None """
    data, mx, Po = [], [], []

    def _x(*path):
        return os.path.join(name, *path)

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
                data.append(('base',[int(x) for x in line[:1]]))
            elif line[0] == '1':
                date.append(('point', list(map(fc.Fraction, line[1:])))
            else:
                continue




"""  for line in stream:
    line = line.split()
    if 'facets' not in line:
        continue
    line, i = line[line.index('facets')+1:], 0
    while i < len(line):
        if not re.match('^\d+$', line[i]):
            break
        i += 1
    data.append([int(x) for x in line[:i]]) """

    with open(name + '.ine', 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po = [list(map(fc.Fraction, xs)) for xs in mx]
        """ A  = [list(map(fc.Fraction, xs[1:])) for xs in mx]
        b  = [-int(xs[0]) for xs in mx] """

    with open(_x('%s_ine.v' % (FNAME,)), 'w') as stream:
        print(PRELUDE_INE, file=stream)
        print('Definition A : seq (seq bigQ) := [::', file=stream)
        for i, v in enumerate(A):
            sep  = ' ' if i == 0 else ';'
            line = '; '.join(map(bigq, v))
            print(f'{sep}  [:: {line}]', file=stream)
        print('].', file=stream)
        print(file=stream)
        print('Definition b : seq bigQ :=', file=stream)
        print('  [:: {}].'.format('; '.join(map(bigq, b))), file=stream)
        print(f'Definition m : nat := {len(A)}%N.', file=stream)
        print(f'Definition n : nat := {len(A[0])}%N.', file=stream)

    i = 0
    while i < len(data):
        index = i // CHUNK; j = 0; fname = '%s_%.4d' % (FNAME, index)
        with open(_x(fname + '.v'), 'w') as stream:
            print(PRELUDE_EXT, file=stream)
            print(f'Definition {fname} : seq (basis * seq (positive * positive)) := [::', file=stream)
            while i < len(data) and j < CHUNK:
                sep  = ' ' if j == 0 else ';'
                line = '; '.join(map(str, data[i]))
                nei = [(t[1][0],t[2][0]) for t in [neighbours(data[i],J) for J in data] if t[0]]
                nei.sort()
                nei.reverse()
                line2 = '; '.join(map(str,nei))
                print(f'{sep}  ([:: {line}], [:: {line2}])', file=stream)
                i += 1; j += 1
            print('].', file=stream)
        with open(_x('job_' + fname + '.v'), 'w') as stream:
            stream.write(JOB.format(name = fname))

    with open(_x('job_' + FNAME + '.v'), 'w') as stream:
        print(PRELUDE_EXT, file=stream)
        for i in range(index+1):
            print('Require job_%s_%.4d.' % (FNAME, i), file=stream)
        print(file=stream)
        print('Definition the_big_and : bool := Eval vm_compute in (', file=stream)
        for i in range(index+1):
            sep = '  ' if i == 0 else '&&'
            print('  %s  job_%s_%.4d.output' % (sep, FNAME, i), file=stream)
        print(').', file=stream)

    shutil.copy2(os.path.join(ROOT, 'efficient_matrix.v'), name)

    with open(_x('_CoqProject'), 'w') as stream:
        print(COQPROJECT_PRELUDE, file=stream)
        print('efficient_matrix.v', file=stream)
        print('%s_ine.v' % (FNAME,), file=stream)
        for i in range(index+1):
            print('%s_%.4d.v' % (FNAME, i), file=stream)
        for i in range(index+1):
            print('job_%s_%.4d.v' % (FNAME, i), file=stream)
        print('job_' + FNAME + '.v', file=stream)

    sp.check_call(
        'coq_makefile -f _CoqProject -o Makefile'.split(),
        cwd = name
    )

    print(f'>>> make TIMED=1 -C {name}')

# --------------------------------------------------------------------
def _main():
    for i in sys.argv[1:]:
        extract(i)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
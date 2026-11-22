"""Boolean policies over interval predicates, NNF, range normalisation, compilers, baselines."""
import random
from collections import Counter
from .covers import *

# formula nodes: ('L', j, set)  ('AND', [..])  ('OR', [..])  ('NOT', f)  ('F',)  ('T',)
class Schema:
    def __init__(self, nbits, beta=1):
        self.nbits = list(nbits)
        self.m = len(nbits)
        self.N = [1 << n for n in nbits]
        self.beta = beta
        self.b = 1 << beta
        self.d = [digits_needed(n, beta) for n in nbits]
    def key_labels_count(self, defined=None):
        js = range(self.m) if defined is None else defined
        return sum(self.d[j] + 1 for j in js)

def leaf(j, ivs):
    return ('L', j, merge_intervals(ivs))

# ---------------- semantics (independent oracle) -----------------
def sem(f, v, neg=False, sch=None):
    """Defined-or-false semantics, computed without compilation."""
    t = f[0]
    if t == 'L':
        j, A = f[1], f[2]
        if j not in v:
            return False
        inside = in_set(v[j], A)
        return (not inside) if neg else inside
    if t == 'NOT':
        return sem(f[1], v, not neg, sch)
    if t == 'AND':
        r = [sem(c, v, neg, sch) for c in f[1]]
        return any(r) if neg else all(r)
    if t == 'OR':
        r = [sem(c, v, neg, sch) for c in f[1]]
        return all(r) if neg else any(r)
    if t == 'F':
        return False
    if t == 'T':
        return True
    raise ValueError(t)

# ---------------- normal forms -----------------
def nnf(f, sch, neg=False):
    t = f[0]
    if t == 'L':
        if not neg:
            return f
        return ('L', f[1], complement_set(f[2], sch.N[f[1]]))
    if t == 'NOT':
        return nnf(f[1], sch, not neg)
    if t in ('AND', 'OR'):
        tt = t if not neg else ('OR' if t == 'AND' else 'AND')
        return (tt, [nnf(c, sch, neg) for c in f[1]])
    return f

def simplify(f, merge):
    """Flatten, fold constants, and (if merge) merge same-attribute leaves under one gate."""
    t = f[0]
    if t == 'L':
        return ('F',) if not f[2] else f
    if t in ('F', 'T'):
        return f
    kids = [simplify(c, merge) for c in f[1]]
    flat = []
    for c in kids:
        if c[0] == t:
            flat.extend(c[1])
        else:
            flat.append(c)
    if merge:
        groups = {}
        rest = []
        for c in flat:
            if c[0] == 'L':
                groups.setdefault(c[1], []).append(c[2])
            else:
                rest.append(c)
        merged = []
        for j, sets in groups.items():
            S = sets[0]
            for X in sets[1:]:
                S = intersect_sets(S, X) if t == 'AND' else union_sets(S, X)
            merged.append(('F',) if not S else ('L', j, S))
        flat = merged + rest
    if t == 'AND':
        flat = [c for c in flat if c[0] != 'T']
        if any(c[0] == 'F' for c in flat):
            return ('F',)
        if not flat:
            return ('T',)
    else:
        flat = [c for c in flat if c[0] != 'F']
        if any(c[0] == 'T' for c in flat):
            return ('T',)
        if not flat:
            return ('F',)
    if len(flat) == 1:
        return flat[0]
    return (t, flat)

# ---------------- label-level compilers -----------------
def and_(a, b):
    if a[0] == 'F' or b[0] == 'F': return ('F',)
    if a[0] == 'T': return b
    if b[0] == 'T': return a
    return ('AND', [a, b])
def or_(a, b):
    if a[0] == 'T' or b[0] == 'T': return ('T',)
    if a[0] == 'F': return b
    if b[0] == 'F': return a
    return ('OR', [a, b])

def compile_cover(f, sch, merge=True):
    """Subtree-cover compiler.  Returns label tree whose leaves are ('X', (j,t,p)), or ('F',)."""
    g = simplify(nnf(f, sch), merge)
    def rec(h):
        if h[0] in ('F', 'T'):
            return h
        if h[0] == 'L':
            j = h[1]
            C = cover_set(h[2], sch.b, sch.d[j])
            xs = [('X', (j, t, p)) for t, p in C]
            return xs[0] if len(xs) == 1 else ('OR', xs)
        kids = [rec(c) for c in h[1]]
        return (h[0], kids)
    out = rec(g)
    return simplify_labels(out)

def simplify_labels(f):
    t = f[0]
    if t in ('X', 'F', 'T'):
        return f
    kids = [simplify_labels(c) for c in f[1]]
    flat = []
    for c in kids:
        if c[0] == t: flat.extend(c[1])
        else: flat.append(c)
    if t == 'AND':
        flat = [c for c in flat if c[0] != 'T']
        if any(c[0] == 'F' for c in flat): return ('F',)
        if not flat: return ('T',)
    else:
        flat = [c for c in flat if c[0] != 'F']
        if any(c[0] == 'T' for c in flat): return ('T',)
        if not flat: return ('F',)
    if len(flat) == 1: return flat[0]
    return (t, flat)

def bitwise_leaf(j, A, sch):
    """Bag-of-bits encoding with linear-size comparators and shared-prefix factoring.
    Key labels are (j,'bit',i,value), i = 0 is the most significant bit."""
    n = sch.nbits[j]; N = sch.N[j]
    def lit(i, val): return ('X', (j, 'bit', i, val))
    def bit(x, i): return (x >> (n - 1 - i)) & 1
    def gt(l, start):   # suffix(x) > suffix(l) over bit positions start..n-1
        G = ('F',)
        for i in range(n - 1, start - 1, -1):
            G = or_(lit(i, 1), G) if bit(l, i) == 0 else and_(lit(i, 1), G)
        return G
    def lt(c, start):   # suffix(x) < suffix(c)
        H = ('F',)
        for i in range(n - 1, start - 1, -1):
            H = or_(lit(i, 0), H) if bit(c, i) == 1 else and_(lit(i, 0), H)
        return H
    terms = ('F',)
    for l, u in A:
        t = 0
        while t < n and bit(l, t) == bit(u, t): t += 1
        term = ('T',)
        for i in range(t): term = and_(term, lit(i, bit(l, i)))
        if t < n:
            mask = (1 << (n - t)) - 1
            lo_s, hi_s = l & mask, u & mask
            if lo_s != 0:                      # x_suffix >= lo_s
                term = and_(term, gt(l, t) if False else _ge(l, t, gt, bit, n, lit))
            if hi_s != mask:                   # x_suffix <= hi_s
                term = and_(term, _le(u, t, lt, bit, n, lit))
        if term[0] == 'T':
            term = or_(lit(0, 0), lit(0, 1))      # attribute merely present
        terms = or_(terms, term)
    return terms

def _ge(l, t, gt, bit, n, lit):
    """suffix(x) >= suffix(l) as suffix(x) > suffix(l)-1 over positions t..n-1 (suffix(l) > 0)."""
    mask = (1 << (n - t)) - 1
    lm1 = ((l & mask) - 1) | (l & ~mask)
    return gt(lm1, t)

def _le(u, t, lt, bit, n, lit):
    """suffix(x) <= suffix(u) as suffix(x) < suffix(u)+1 (suffix(u) < all-ones)."""
    mask = (1 << (n - t)) - 1
    up1 = ((u & mask) + 1) | (u & ~mask)
    return lt(up1, t)

def compile_bitwise(f, sch):
    g = simplify(nnf(f, sch), False)
    def rec(h):
        if h[0] in ('F', 'T'): return h
        if h[0] == 'L': return bitwise_leaf(h[1], h[2], sch)
        return (h[0], [rec(c) for c in h[1]])
    return simplify_labels(rec(g))

def unary_rows(f, sch):
    """Row count of the one-attribute-per-value encoding (not materialised)."""
    g = simplify(nnf(f, sch), False)
    def rec(h):
        if h[0] == 'L': return set_size(h[2])
        if h[0] in ('F', 'T'): return 0
        return sum(rec(c) for c in h[1])
    return rec(g)

# ---------------- metrics -----------------
def leaves(f):
    if f[0] == 'X': return [f[1]]
    if f[0] in ('F', 'T'): return []
    out = []
    for c in f[1]: out.extend(leaves(c))
    return out

def rows(f): return len(leaves(f))
def multiplicity(f):
    c = Counter(leaves(f))
    return max(c.values()) if c else 0

def key_labelset(v, sch):
    S = set()
    for j, val in v.items():
        for t, p in key_path(val, sch.b, sch.d[j]):
            S.add((j, t, p))
    return S

def key_labelset_bitwise(v, sch):
    S = set()
    for j, val in v.items():
        n = sch.nbits[j]
        for i in range(n):
            S.add((j, 'bit', i, (val >> (n - 1 - i)) & 1))
    return S

def eval_labels(f, S):
    t = f[0]
    if t == 'X': return f[1] in S
    if t == 'T': return True
    if t == 'F': return False
    r = [eval_labels(c, S) for c in f[1]]
    return all(r) if t == 'AND' else any(r)

def min_used(f, S):
    """Fewest leaves needed to satisfy f with label set S (None if unsatisfied)."""
    t = f[0]
    if t == 'X': return 1 if f[1] in S else None
    if t == 'T': return 0
    if t == 'F': return None
    r = [min_used(c, S) for c in f[1]]
    if t == 'AND':
        return None if any(x is None for x in r) else sum(r)
    r = [x for x in r if x is not None]
    return min(r) if r else None

# ---------------- random policies & satisfying assignments -----------------
def random_leaf(sch, rng, mix=(0.35, 0.35, 0.30)):
    j = rng.randrange(sch.m)
    N = sch.N[j]; n = sch.nbits[j]
    r = rng.random()
    if r < mix[0]:
        c = rng.randrange(N); A = [(c, c)]
    elif r < mix[0] + mix[1]:
        w = rng.randint(2, 1 << max(1, n // 2))
        l = rng.randrange(0, N - w + 1); A = [(l, l + w - 1)]
    else:
        a, b2 = sorted((rng.randrange(N), rng.randrange(N)))
        A = [(a, b2)]
    return leaf(j, A)

def random_policy(k, sch, rng, p_and=0.5, p_not_leaf=0.15, p_not_gate=0.04, mix=(0.35, 0.35, 0.30)):
    if k == 1:
        f = random_leaf(sch, rng, mix)
        return ('NOT', f) if rng.random() < p_not_leaf else f
    k1 = rng.randint(1, k - 1)
    a = random_policy(k1, sch, rng, p_and, p_not_leaf, p_not_gate, mix)
    b2 = random_policy(k - k1, sch, rng, p_and, p_not_leaf, p_not_gate, mix)
    g = ('AND' if rng.random() < p_and else 'OR', [a, b2])
    return ('NOT', g) if rng.random() < p_not_gate else g

def satisfying_assignment(f, sch, rng):
    """Random assignment satisfying f (defined-or-false semantics) or None."""
    g = simplify(nnf(f, sch), False)
    def solve(h, cons):
        t = h[0]
        if t == 'T': return cons
        if t == 'F': return None
        if t == 'L':
            j = h[1]
            cur = cons.get(j, ((0, sch.N[j] - 1),))
            S = intersect_sets(cur, h[2])
            if not S: return None
            c2 = dict(cons); c2[j] = S
            return c2
        if t == 'AND':
            kids = list(h[1]); rng.shuffle(kids)
            for c in kids:
                cons = solve(c, cons)
                if cons is None: return None
            return cons
        kids = list(h[1]); rng.shuffle(kids)
        for c in kids:
            r = solve(c, cons)
            if r is not None: return r
        return None
    cons = solve(g, {})
    if cons is None: return None
    v = {}
    for j, S in cons.items():
        l, u = S[rng.randrange(len(S))]
        v[j] = rng.randint(l, u)
    for j in range(sch.m):
        if j not in v and rng.random() < 0.5:
            v[j] = rng.randrange(sch.N[j])
    return v

def random_assignment(sch, rng, p_def=0.8):
    return {j: rng.randrange(sch.N[j]) for j in range(sch.m) if rng.random() < p_def}

import sys, json, random, time, statistics as st
import os
from scope.policy import *

R = {}
def mean(x): return sum(x) / len(x) if x else float('nan')

# ---------- E0: correctness (randomised, large) ----------
def e0():
    rng = random.Random(2026)
    tot = bad = 0; pol = 0
    for trial in range(6000):
        beta = rng.choice([1, 1, 2, 3, 4])
        sch = Schema([rng.choice([5, 6, 8, 9]) for _ in range(3)], beta)
        k = rng.randint(1, 12)
        f = random_policy(k, sch, rng, p_not_leaf=0.25, p_not_gate=0.1)
        C = compile_cover(f, sch, True); C0 = compile_cover(f, sch, False); B = compile_bitwise(f, sch)
        pol += 1
        vs = [random_assignment(sch, rng) for _ in range(20)]
        sa = satisfying_assignment(f, sch, rng)
        if sa: vs.append(sa)
        # boundary-adjacent assignments
        for _ in range(10):
            g = random_leaf(sch, rng); j = g[1]; l, u = g[2][0]
            v = random_assignment(sch, rng, 0.9); v[j] = rng.choice([max(0, l - 1), l, u, min(sch.N[j] - 1, u + 1)])
            vs.append(v)
        for v in vs:
            o = sem(f, v)
            S = key_labelset(v, sch); Sb = key_labelset_bitwise(v, sch)
            for X, SS in ((C, S), (C0, S), (B, Sb)):
                tot += 1
                if eval_labels(X, SS) != o: bad += 1
    R['e0'] = dict(policies=pol, evaluations=tot, mismatches=bad)
    print('E0', R['e0'])

# ---------- E1: single interval, n = 16 ----------
def e1():
    rng = random.Random(1)
    n = 16; N = 1 << n
    out = []
    schs = {b: Schema([n], b) for b in (1, 2, 4)}
    for s in range(0, n):
        w = 1 << s
        acc = {k: [] for k in ('b2', 'b4', 'b16', 'bit', 'bit_used')}
        for _ in range(1500):
            l = rng.randrange(0, N - w + 1); f = ('L', 0, ((l, l + w - 1),))
            acc['b2'].append(rows(compile_cover(f, schs[1])))
            acc['b4'].append(rows(compile_cover(f, schs[2])))
            acc['b16'].append(rows(compile_cover(f, schs[4])))
            B = compile_bitwise(f, schs[1]); acc['bit'].append(rows(B))
            v = {0: rng.randint(l, l + w - 1)}
            acc['bit_used'].append(min_used(B, key_labelset_bitwise(v, schs[1])))
        out.append(dict(log2w=s, width=w, **{k: mean(v) for k, v in acc.items()}, unary=w))
    # uniformly random intervals
    acc = {k: [] for k in ('b2', 'b4', 'b16', 'bit')}
    for _ in range(4000):
        a, b2 = sorted((rng.randrange(N), rng.randrange(N))); f = ('L', 0, ((a, b2),))
        acc['b2'].append(rows(compile_cover(f, schs[1]))); acc['b4'].append(rows(compile_cover(f, schs[2])))
        acc['b16'].append(rows(compile_cover(f, schs[4]))); acc['bit'].append(rows(compile_bitwise(f, schs[1])))
    R['e1'] = dict(n=n, by_width=out, uniform={k: mean(v) for k, v in acc.items()})
    # worst cases (exhaustive, n=8)
    n8 = 8; N8 = 256; sch8 = Schema([n8], 1); worst = 0; wb = 0; s_all = []; sb = []
    for l in range(N8):
        for u in range(l, N8):
            f = ('L', 0, ((l, u),)); r = rows(compile_cover(f, sch8)); worst = max(worst, r); s_all.append(r)
            rb = rows(compile_bitwise(f, sch8)); wb = max(wb, rb); sb.append(rb)
    R['e1']['exhaustive8'] = dict(worst_cover=worst, bound=cover_bound(2, 8), mean_cover=mean(s_all), worst_bit=wb, mean_bit=mean(sb))
    print('E1 done', R['e1']['uniform'], R['e1']['exhaustive8'])

# ---------- E2: random Boolean policies ----------
def run_strats(f, sch, rng):
    rec = {}
    t0 = time.perf_counter(); C = compile_cover(f, sch, True); tc = time.perf_counter() - t0
    t0 = time.perf_counter(); C0 = compile_cover(f, sch, False); tn = time.perf_counter() - t0
    t0 = time.perf_counter(); B = compile_bitwise(f, sch); tb = time.perf_counter() - t0
    if C[0] == 'F' or C0[0] == 'F' or B[0] == 'F':
        return None
    v = satisfying_assignment(f, sch, rng)
    if v is None: return None
    assert sem(f, v)
    S = key_labelset(v, sch); Sb = key_labelset_bitwise(v, sch)
    rec['norm'] = dict(rows=rows(C), mu=multiplicity(C), used=min_used(C, S), ms=tc * 1e3)
    rec['naive'] = dict(rows=rows(C0), mu=multiplicity(C0), used=min_used(C0, S), ms=tn * 1e3)
    rec['bit'] = dict(rows=rows(B), mu=multiplicity(B), used=min_used(B, Sb), ms=tb * 1e3)
    rec['unary'] = dict(rows=unary_rows(f, sch))
    return rec

def e2(name, widths, ks, reps, seed):
    rng = random.Random(seed)
    sch = Schema(widths, 1)
    res = []
    for k in ks:
        acc = {s: {m: [] for m in ('rows', 'mu', 'used', 'ms')} for s in ('norm', 'naive', 'bit')}
        un = []
        got = 0
        while got < reps:
            f = random_policy(k, sch, rng)
            r = run_strats(f, sch, rng)
            if r is None: continue
            got += 1
            for s in acc:
                for m in acc[s]: acc[s][m].append(r[s][m])
            un.append(r['unary']['rows'])
        row = dict(k=k)
        for s in acc:
            for m in acc[s]:
                row[f'{s}_{m}'] = mean(acc[s][m])
                row[f'{s}_{m}_max'] = max(acc[s][m])
                row[f'{s}_{m}_sd'] = st.pstdev(acc[s][m])
        row['unary_rows'] = mean(un)
        row['norm_gain'] = 1 - row['norm_rows'] / row['naive_rows']
        res.append(row)
        print(name, k, round(row['norm_rows'], 1), round(row['naive_rows'], 1), round(row['bit_rows'], 1), 'mu', round(row['norm_mu'], 2), round(row['naive_mu'], 2), round(row['bit_mu'], 2))
    R[name] = dict(widths=widths, reps=reps, rows=res, keylabels_cover=sch.key_labels_count(), keylabels_bit=sum(widths))

# ---------- E3: radix ----------
def e3():
    rng = random.Random(3)
    n = 32; N = 1 << n; out = []
    for beta in (1, 2, 3, 4, 5, 8):
        sch = Schema([n], beta); d = sch.d[0]
        if (1 << (beta * d)) < N: raise SystemExit
        uni = []; nar = []; eq = []
        for _ in range(3000):
            a, b2 = sorted((rng.randrange(N), rng.randrange(N))); uni.append(rows(compile_cover(('L', 0, ((a, b2),)), sch)))
            w = rng.randint(2, 256); l = rng.randrange(0, N - w); nar.append(rows(compile_cover(('L', 0, ((l, l + w - 1),)), sch)))
            c = rng.randrange(N); eq.append(rows(compile_cover(('L', 0, ((c, c),)), sch)))
        worst = rows(compile_cover(('L', 0, ((1, N - 2),)), sch))
        out.append(dict(beta=beta, b=1 << beta, d=d, key_labels=d + 1, bound=cover_bound(1 << beta, d), worst=worst,
                        mean_uniform=mean(uni), mean_narrow=mean(nar), mean_eq=mean(eq)))
        print('radix', out[-1])
    R['e3'] = out

# ---------- E4: case studies ----------
def e4():
    # attributes: 0 zone(16) 1 minute(11) 2 clearance(8) 3 firmware(16) 4 role(8) 5 ward(8)
    sch = Schema([16, 11, 8, 16, 8, 8], 1)
    L = lambda j, l, u=None: ('L', j, merge_intervals([(l, l if u is None else u)]))
    cs = {}
    cs['CS1 grid operator'] = ('AND', [('OR', [L(0, 1200, 1263), L(0, 2048, 2303)]), L(2, 3, 7), ('NOT', L(4, 9))])
    cs['CS2 hospital ward'] = ('OR', [('AND', [L(4, 4), L(5, 10, 19)]), ('AND', [L(4, 6), L(5, 10, 19), L(1, 0, 480)]), L(2, 9, 15)])
    cs['CS3 firmware campaign'] = ('AND', [L(3, 20300, 20999), ('OR', [L(0, 4000, 4999), L(0, 5000, 5499), L(0, 7000, 7099)]), L(1, 480, 1020), L(1, 600, 1200)])
    cs['CS4 maintenance window'] = ('AND', [('OR', [L(1, 0, 359), L(1, 1380, 2047)]), ('OR', [('AND', [L(4, 2), L(5, 30, 39)]), ('AND', [L(4, 3), L(5, 30, 59)])]), ('NOT', L(2, 0, 1))])
    out = []
    rng = random.Random(4)
    for name, f in cs.items():
        row = dict(name=name)
        C = compile_cover(f, sch, True); C0 = compile_cover(f, sch, False); B = compile_bitwise(f, sch)
        v = satisfying_assignment(f, sch, rng); assert v is not None and sem(f, v)
        S = key_labelset(v, sch); Sb = key_labelset_bitwise(v, sch)
        assert eval_labels(C, S) and eval_labels(C0, S) and eval_labels(B, Sb)
        row.update(norm_rows=rows(C), naive_rows=rows(C0), bit_rows=rows(B), unary_rows=unary_rows(f, sch),
                   norm_mu=multiplicity(C), naive_mu=multiplicity(C0), bit_mu=multiplicity(B),
                   norm_used=min_used(C, S), naive_used=min_used(C0, S), bit_used=min_used(B, Sb))
        out.append(row); print(row)
    R['e4'] = dict(rows=out, keylabels_cover=sch.key_labels_count(), keylabels_bit=sum(sch.nbits))

if __name__ == '__main__':
    t0 = time.time()
    e0(); e1()
    e2('e2', [16, 16, 16, 8, 8, 8], [1, 2, 4, 8, 12, 16, 24, 32], 300, 11)
    e2('e2dense', [16, 16], [2, 4, 8, 16, 32], 300, 12)
    e3(); e4()
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'compiler_results.json')
    json.dump(R, open(out, 'w'), indent=1)
    print('total', time.time() - t0)

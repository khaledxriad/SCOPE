import sys, os, json, time, random, statistics as st
from scope.policy import *
from scope.abe import *
from scope import bn254
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'proto_results.json')

def med(f, n=15):
    ts = []
    for _ in range(n):
        t0 = time.perf_counter(); f(); ts.append(time.perf_counter() - t0)
    return st.median(ts) * 1e3

out = {}
rng = random.Random(77)
# ---- primitives ----
a = rng.randrange(1, R); Pa = g1mul(G1, 12345); Qa = g2mul(G2, 6789)
f_ml = bn254.miller(Qa, Pa)
out['prim'] = dict(
    g1mul=med(lambda: g1mul(Pa, a)), g2mul=med(lambda: g2mul(Qa, a)),
    hash_g2=med(lambda: hash_to_g2(b'label-%d' % rng.randrange(10**9)), 9),
    miller=med(lambda: bn254.miller(Qa, Pa)), final_exp=med(lambda: bn254.final_exp(f_ml)),
    pairing=med(lambda: pairing(Pa, Qa)), gt_exp=med(lambda: gt_pow(f12inv(f_ml), a), 7),
    f12mul=med(lambda: f12mul(f_ml, f_ml), 200))
print('prim', out['prim'], flush=True)
P_ = out['prim']

def run_policy(f, sch, strat, abe, v, reps=1):
    if strat == 'norm': T = compile_cover(f, sch, True)
    elif strat == 'naive': T = compile_cover(f, sch, False)
    else: T = compile_bitwise(f, sch)
    S = key_labelset(v, sch) if strat != 'bit' else key_labelset_bitwise(v, sch)
    labs = sorted(S, key=repr)
    t0 = time.perf_counter(); sk = abe.keygen(labs); tk = time.perf_counter() - t0
    all_labels = set(leaves(T))
    t0 = time.perf_counter()
    for lab in all_labels | set(labs): abe.H(lab)
    th = time.perf_counter() - t0
    t0 = time.perf_counter(); ct, K = abe.encrypt(T); te = time.perf_counter() - t0
    t0 = time.perf_counter(); K2 = abe.decrypt(ct, sk, S); td = time.perf_counter() - t0
    assert K2 == K, 'decryption failed'
    used = min_used(T, S)
    return dict(rows=rows(T), used=used, mu=multiplicity(T), keygen_ms=tk * 1e3, hash_ms=th * 1e3, enc_ms=te * 1e3, dec_ms=td * 1e3,
                key_bytes=abe.key_size(sk), ct_bytes=abe.ct_size(ct), key_labels=len(labs),
                model_enc=(len(ct['leaves']) * (P_['g1mul'] + P_['g2mul']) + P_['g1mul'] + P_['gt_exp']),
                model_dec=((1 + 2 * used) * P_['miller'] + P_['final_exp'] + 2 * used * P_['f12mul']),
                model_key=(2 * P_['g2mul'] + len(labs) * (P_['g2mul'] + P_['g1mul'])))

# ---- case studies ----
sch = Schema([16, 11, 8, 16, 8, 8], 1)
L = lambda j, l, u=None: ('L', j, merge_intervals([(l, l if u is None else u)]))
cs = {
 'CS1 grid operator': ('AND', [('OR', [L(0, 1200, 1263), L(0, 2048, 2303)]), L(2, 3, 7), ('NOT', L(4, 9))]),
 'CS2 hospital ward': ('OR', [('AND', [L(4, 4), L(5, 10, 19)]), ('AND', [L(4, 6), L(5, 10, 19), L(1, 0, 480)]), L(2, 9, 15)]),
 'CS3 firmware campaign': ('AND', [L(3, 20300, 20999), ('OR', [L(0, 4000, 4999), L(0, 5000, 5499), L(0, 7000, 7099)]), L(1, 480, 1020), L(1, 600, 1200)]),
 'CS4 maintenance window': ('AND', [('OR', [L(1, 0, 359), L(1, 1380, 2047)]), ('OR', [('AND', [L(4, 2), L(5, 30, 39)]), ('AND', [L(4, 3), L(5, 30, 59)])]), ('NOT', L(2, 0, 1))]),
}
out['cs'] = []
for name, f in cs.items():
    r2 = random.Random(5)
    v = satisfying_assignment(f, sch, r2)
    for j in range(sch.m):
        if j not in v: v[j] = r2.randrange(sch.N[j])
    assert sem(f, v)
    for strat in ('norm', 'naive', 'bit'):
        abe = BSW(3); abe.setup()
        r = run_policy(f, sch, strat, abe, v); r.update(case=name, strat=strat)
        out['cs'].append(r); print(name, strat, {k: (round(x, 1) if isinstance(x, float) else x) for k, x in r.items()}, flush=True)
json.dump(out, open(OUT, 'w'), indent=1)

# ---- scaling on random policies ----
sch2 = Schema([16, 16, 16, 8, 8, 8], 1)
out['scale'] = []
rr = random.Random(99)
for k in (2, 4, 8, 16):
    got = 0
    while got < 3:
        f = random_policy(k, sch2, rr)
        T = compile_cover(f, sch2, True); Tb = compile_bitwise(f, sch2)
        if T[0] == 'F' or Tb[0] == 'F': continue
        v = satisfying_assignment(f, sch2, rr)
        if v is None: continue
        for j in range(sch2.m):
            if j not in v: v[j] = rr.randrange(sch2.N[j])
        got += 1
        for strat in ('norm', 'bit'):
            abe = BSW(11 + got); abe.setup()
            r = run_policy(f, sch2, strat, abe, v); r.update(k=k, strat=strat); out['scale'].append(r)
            print('scale', k, strat, {kk: (round(x, 1) if isinstance(x, float) else x) for kk, x in r.items() if kk in ('rows', 'used', 'enc_ms', 'dec_ms', 'keygen_ms', 'model_enc', 'model_dec')}, flush=True)
        json.dump(out, open(OUT, 'w'), indent=1)
json.dump(out, open(OUT, 'w'), indent=1)
print('done')

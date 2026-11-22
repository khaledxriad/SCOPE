"""Type-3 BSW07-style CP-ABE (key encapsulation) on BN254, access trees with AND/OR gates.
Research prototype used to calibrate and validate the compiler; not constant-time, not for production."""
import hashlib, random, time
from .bn254 import *

G1_BYTES, G2_BYTES = 32, 64      # compressed point sizes on BN254

class BSW:
    def __init__(self, seed=0):
        self.rng = random.Random(seed)
        self.hcache = {}
    def rnd(self): return self.rng.randrange(1, R)
    def H(self, label):
        key = repr(label)
        if key not in self.hcache:
            self.hcache[key] = hash_to_g2(key.encode())
        return self.hcache[key]
    def setup(self):
        alpha, beta = self.rnd(), self.rnd()
        self.beta_inv = pow(beta, -1, R)
        self.alpha = alpha
        self.h1 = g1mul(G1, beta)
        self.e_alpha = gt_pow(pairing(G1, G2), alpha)
        return dict(h1=self.h1, e_alpha=self.e_alpha)
    def keygen(self, labels):
        r = self.rnd()
        D = g2mul(G2, (self.alpha + r) * self.beta_inv % R)
        gr = g2mul(G2, r)
        comp = {}
        for lab in labels:
            rj = self.rnd()
            comp[lab] = (g2add(gr, g2mul(self.H(lab), rj)), g1mul(G1, rj))
        return dict(D=D, comp=comp)
    def key_size(self, sk):
        return G2_BYTES + len(sk['comp']) * (G2_BYTES + G1_BYTES)
    # ---- encryption ----
    def encrypt(self, tree):
        s = self.rnd()
        leaves = []
        def share(node, val):
            t = node[0]
            if t == 'X':
                lab = node[1]
                leaves.append((node, g1mul(G1, val), g2mul(self.H(lab), val)))
                return ('X', node[1], len(leaves) - 1)
            if t == 'OR':
                return ('OR', [share(c, val) for c in node[1]])
            parts = [self.rnd() for _ in node[1][:-1]]
            parts.append((val - sum(parts)) % R)
            return ('AND', [share(c, v) for c, v in zip(node[1], parts)])
        stree = share(tree, s)
        K = gt_pow(self.e_alpha, s)
        ct = dict(C=g1mul(self.h1, s), tree=stree, leaves=[(a, b) for _, a, b in leaves])
        return ct, hashlib.sha256(gt_bytes(K)).digest()
    def ct_size(self, ct):
        return G1_BYTES + len(ct['leaves']) * (G1_BYTES + G2_BYTES)
    # ---- decryption ----
    def plan(self, tree, S):
        t = tree[0]
        if t == 'X': return (1, [tree[2]]) if tree[1] in S else None
        subs = [self.plan(c, S) for c in tree[1]]
        if t == 'AND':
            if any(x is None for x in subs): return None
            return (sum(c for c, _ in subs), [i for _, l in subs for i in l])
        subs = [x for x in subs if x is not None]
        return min(subs, key=lambda x: x[0]) if subs else None
    def decrypt(self, ct, sk, S):
        pl = self.plan(ct['tree'], S)
        if pl is None: return None
        f = miller(sk['D'], ct['C'])
        labs = {}
        def collect(node):
            if node[0] == 'X': labs[node[2]] = node[1]
            else:
                for c in node[1]: collect(c)
        collect(ct['tree'])
        for idx in pl[1]:
            Cy, Cpy = ct['leaves'][idx]
            Dj, Dpj = sk['comp'][labs[idx]]
            f = f12mul(f, miller(Cpy, Dpj))
            f = f12mul(f, miller(Dj, g1neg(Cy)))
        K = final_exp(f)
        return hashlib.sha256(gt_bytes(K)).digest()

def uniquify(tree):
    """Give every occurrence of a label its own copy index (for one-use bases)."""
    cnt = {}
    def rec(n):
        if n[0] == 'X':
            c = cnt.get(n[1], 0) + 1; cnt[n[1]] = c
            return ('X', (n[1], c))
        return (n[0], [rec(x) for x in n[1]])
    return rec(tree), (max(cnt.values()) if cnt else 0)

if __name__ == '__main__':
    from .policy import *
    sch = Schema([6, 6], 1)
    f = ('AND', [('L', 0, ((10, 40),)), ('OR', [('L', 1, ((3, 3),)), ('NOT', ('L', 1, ((0, 31),)))])])
    tree = compile_cover(f, sch)
    print('rows', rows(tree))
    abe = BSW(1); abe.setup()
    for v, expect in [({0: 20, 1: 3}, True), ({0: 20, 1: 40}, True), ({0: 20, 1: 5}, False), ({0: 41, 1: 3}, False), ({0: 20}, False)]:
        S = key_labelset(v, sch)
        sk = abe.keygen(sorted(S))
        t0 = time.time(); ct, K = abe.encrypt(tree); te = time.time() - t0
        t0 = time.time(); K2 = abe.decrypt(ct, sk, S); td = time.time() - t0
        ok = (K2 == K) if expect else (K2 is None or K2 != K)
        print(v, 'expected', expect, 'recovered', K2 == K, 'OK' if ok else 'FAIL', round(te, 3), round(td, 3))

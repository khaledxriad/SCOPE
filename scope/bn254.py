"""Minimal pure-Python BN254 (alt_bn128) optimal-ate pairing. Research prototype, NOT constant-time."""
import hashlib, random

U = 4965661367192848881
P = 36*U**4 + 36*U**3 + 24*U**2 + 6*U + 1
R = 36*U**4 + 36*U**3 + 18*U**2 + 6*U + 1
ATE = 6*U + 2
assert P == 21888242871839275222246405745257275088696311157297823662689037894645226208583
H2 = 2*P - R          # cofactor of the twist group

# ---------------- Fp2 = Fp[i]/(i^2+1) ----------------
def f2add(a, b): return ((a[0]+b[0]) % P, (a[1]+b[1]) % P)
def f2sub(a, b): return ((a[0]-b[0]) % P, (a[1]-b[1]) % P)
def f2neg(a): return ((-a[0]) % P, (-a[1]) % P)
def f2mul(a, b): return ((a[0]*b[0]-a[1]*b[1]) % P, (a[0]*b[1]+a[1]*b[0]) % P)
def f2sqr(a): return (((a[0]+a[1])*(a[0]-a[1])) % P, (2*a[0]*a[1]) % P)
def f2inv(a):
    n = pow((a[0]*a[0]+a[1]*a[1]) % P, -1, P)
    return ((a[0]*n) % P, (-a[1]*n) % P)
def f2conj(a): return (a[0], (-a[1]) % P)
def f2sc(a, k): return ((a[0]*k) % P, (a[1]*k) % P)
def f2pow(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = f2mul(r, a)
        a = f2sqr(a); e >>= 1
    return r
XI = (9, 1)
B1 = 3
B2 = f2mul((3, 0), f2inv(XI))

def f2sqrt(a):
    """sqrt in Fp2 for p = 3 mod 4 (Adj-Rodriguez-Henriquez, alg. 9); None if non-residue."""
    if a == (0, 0): return (0, 0)
    a1 = f2pow(a, (P-3)//4)
    alpha = f2mul(f2sqr(a1), a)
    a0 = f2mul(f2pow(alpha, P), alpha)
    if a0 == (P-1, 0): return None
    x0 = f2mul(a1, a)
    if alpha == (P-1, 0):
        return f2mul((0, 1), x0)
    b = f2pow(f2add((1, 0), alpha), (P-1)//2)
    return f2mul(b, x0)

# ---------------- G1: y^2 = x^3 + 3 over Fp (affine, None = infinity) ----------------
G1 = (1, 2)
def g1add(A, B):
    if A is None: return B
    if B is None: return A
    if A[0] == B[0]:
        if (A[1]+B[1]) % P == 0: return None
        l = 3*A[0]*A[0] * pow(2*A[1], -1, P) % P
    else:
        l = (B[1]-A[1]) * pow(B[0]-A[0], -1, P) % P
    x = (l*l - A[0] - B[0]) % P
    return (x, (l*(A[0]-x) - A[1]) % P)
def g1neg(A): return None if A is None else (A[0], (-A[1]) % P)
def g1mul(A, k):
    k %= R
    Rr = None
    while k:
        if k & 1: Rr = g1add(Rr, A)
        A = g1add(A, A); k >>= 1
    return Rr

# ---------------- G2: twist y^2 = x^3 + 3/(9+i) over Fp2 ----------------
def g2add(A, B):
    if A is None: return B
    if B is None: return A
    if A[0] == B[0]:
        if f2add(A[1], B[1]) == (0, 0): return None
        l = f2mul(f2sc(f2sqr(A[0]), 3), f2inv(f2sc(A[1], 2)))
    else:
        l = f2mul(f2sub(B[1], A[1]), f2inv(f2sub(B[0], A[0])))
    x = f2sub(f2sub(f2sqr(l), A[0]), B[0])
    return (x, f2sub(f2mul(l, f2sub(A[0], x)), A[1]))
def g2neg(A): return None if A is None else (A[0], f2neg(A[1]))
def g2mul(A, k, reduce=True):
    if reduce: k %= R
    Rr = None
    while k:
        if k & 1: Rr = g2add(Rr, A)
        A = g2add(A, A); k >>= 1
    return Rr
def g2_on_curve(Q): return f2sub(f2sqr(Q[1]), f2add(f2mul(f2sqr(Q[0]), Q[0]), B2)) == (0, 0)

def hash_to_g2(data: bytes):
    c = 0
    while True:
        h0 = int.from_bytes(hashlib.sha512(data + b'|0|' + bytes([c])).digest(), 'big') % P
        h1 = int.from_bytes(hashlib.sha512(data + b'|1|' + bytes([c])).digest(), 'big') % P
        x = (h0, h1)
        y = f2sqrt(f2add(f2mul(f2sqr(x), x), B2))
        if y is not None:
            Q = g2mul((x, y), H2, reduce=False)
            if Q is not None: return Q
        c += 1

def find_g2():
    c = 1
    while True:
        x = (c, 1)
        y = f2sqrt(f2add(f2mul(f2sqr(x), x), B2))
        if y is not None:
            Q = g2mul((x, y), H2, reduce=False)
            if Q is not None: return Q
        c += 1
G2 = find_g2()
assert g2_on_curve(G2) and g2mul(G2, R, reduce=False) is None

# ---------------- Fp12 = Fp[w]/(w^12 - 18 w^6 + 82), list of 12 ints ----------------
ONE12 = [1] + [0]*11
def f12mul(a, b):
    c = [0]*23
    for i in range(12):
        ai = a[i]
        if ai:
            for j in range(12):
                c[i+j] += ai*b[j]
    for k in range(22, 11, -1):
        t = c[k]
        if t:
            c[k-6] += 18*t; c[k-12] -= 82*t
    return [x % P for x in c[:12]]
def f12sqr(a):
    c = [0]*23
    for i in range(12):
        ai = a[i]
        if ai:
            c[2*i] += ai*ai
            ai2 = 2*ai
            for j in range(i+1, 12):
                c[i+j] += ai2*a[j]
    for k in range(22, 11, -1):
        t = c[k]
        if t:
            c[k-6] += 18*t; c[k-12] -= 82*t
    return [x % P for x in c[:12]]
SPARSE = (0, 1, 3, 7, 9)
def f12mul_sparse(a, line):
    c = [0]*23
    for j in SPARSE:
        lj = line[j]
        if lj:
            for i in range(12):
                c[i+j] += a[i]*lj
    for k in range(22, 11, -1):
        t = c[k]
        if t:
            c[k-6] += 18*t; c[k-12] -= 82*t
    return [x % P for x in c[:12]]
def f12pow(a, e):
    r = ONE12
    for bit in bin(e)[2:]:
        r = f12sqr(r)
        if bit == '1': r = f12mul(r, a)
    return r
def f12inv(a):
    cols = []; v = list(a)
    for _ in range(12):
        cols.append(v)
        t = v[11]
        v = [0] + v[:11]
        if t:
            v[6] = (v[6] + 18*t) % P; v[0] = (v[0] - 82*t) % P
    M = [[cols[k][i] for k in range(12)] + [1 if i == 0 else 0] for i in range(12)]
    for c in range(12):
        piv = next(r for r in range(c, 12) if M[r][c] % P)
        M[c], M[piv] = M[piv], M[c]
        inv = pow(M[c][c], -1, P)
        M[c] = [(x*inv) % P for x in M[c]]
        for r in range(12):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f*y) % P for x, y in zip(M[r], M[c])]
    return [M[i][12] for i in range(12)]

# ---------------- pairing ----------------
C1 = f2pow(XI, (P-1)//3)
C2 = f2pow(XI, (P-1)//2)
def twist_frob(Q):
    return (f2mul(f2conj(Q[0]), C1), f2mul(f2conj(Q[1]), C2))

def _line(lam, xT, yT, xP, yP):
    mu = f2sub(f2mul(lam, xT), yT)
    l = [0]*12
    l[0] = yP % P
    t = f2sc(lam, (-xP) % P)
    l[1] = (t[0] - 9*t[1]) % P; l[7] = t[1]
    l[3] = (mu[0] - 9*mu[1]) % P; l[9] = mu[1]
    return l

ATE_BITS = bin(ATE)[3:]
def miller(Q, Pt):
    """Miller loop f_{6u+2,Q}(P) with Frobenius corrections; Q in G2 (twist), Pt in G1."""
    if Q is None or Pt is None: return ONE12
    xP, yP = Pt
    T = Q; f = ONE12
    for bit in ATE_BITS:
        lam = f2mul(f2sc(f2sqr(T[0]), 3), f2inv(f2sc(T[1], 2)))
        f = f12mul_sparse(f12sqr(f), _line(lam, T[0], T[1], xP, yP))
        x3 = f2sub(f2sqr(lam), f2sc(T[0], 2))
        T = (x3, f2sub(f2mul(lam, f2sub(T[0], x3)), T[1]))
        if bit == '1':
            lam = f2mul(f2sub(Q[1], T[1]), f2inv(f2sub(Q[0], T[0])))
            f = f12mul_sparse(f, _line(lam, T[0], T[1], xP, yP))
            x3 = f2sub(f2sub(f2sqr(lam), T[0]), Q[0])
            T = (x3, f2sub(f2mul(lam, f2sub(T[0], x3)), T[1]))
    Q1 = twist_frob(Q); Q2 = twist_frob(Q1); nQ2 = (Q2[0], f2neg(Q2[1]))
    lam = f2mul(f2sub(Q1[1], T[1]), f2inv(f2sub(Q1[0], T[0])))
    f = f12mul_sparse(f, _line(lam, T[0], T[1], xP, yP))
    x3 = f2sub(f2sub(f2sqr(lam), T[0]), Q1[0])
    T = (x3, f2sub(f2mul(lam, f2sub(T[0], x3)), T[1]))
    lam = f2mul(f2sub(nQ2[1], T[1]), f2inv(f2sub(nQ2[0], T[0])))
    f = f12mul_sparse(f, _line(lam, T[0], T[1], xP, yP))
    return f

HARD = (P**4 - P**2 + 1) // R
assert (P**4 - P**2 + 1) % R == 0
def final_exp(f):
    fc = [(-x) % P if i & 1 else x for i, x in enumerate(f)]
    t = f12mul(fc, f12inv(f))
    t = f12mul(f12pow(t, P*P), t)
    return f12pow(t, HARD)

def pairing(Pt, Q):
    return final_exp(miller(Q, Pt))
def multi_pairing(pairs):
    f = ONE12
    for Pt, Q in pairs:
        f = f12mul(f, miller(Q, Pt))
    return final_exp(f)
def gt_mul(a, b): return f12mul(a, b)
def gt_pow(a, e): return f12pow(a, e % R)
def gt_bytes(a): return b''.join(x.to_bytes(32, 'big') for x in a)

if __name__ == '__main__':
    import time
    rng = random.Random(1)
    t = time.perf_counter(); e = pairing(G1, G2); print('pairing', time.perf_counter()-t)
    assert e != ONE12 and f12pow(e, R) == ONE12
    a, b = rng.randrange(1, R), rng.randrange(1, R)
    e2 = pairing(g1mul(G1, a), g2mul(G2, b))
    assert e2 == gt_pow(e, a*b), 'bilinearity failed'
    assert pairing(g1mul(G1, a), G2) == pairing(G1, g2mul(G2, a))
    print('bilinear OK')

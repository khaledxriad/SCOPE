"""Radix-b subtree covers for integer intervals (the 'subtree-cover' machinery)."""
from functools import lru_cache

def node_range(t, p, b, d):
    w = b ** (d - t)
    return p * w, (p + 1) * w - 1

def key_path(v, b, d):
    """Labels (t, prefix) of the root-to-leaf path of value v, levels 0..d."""
    out = []
    for t in range(d + 1):
        out.append((t, v // (b ** (d - t))))
    return out

def cover_interval(l, u, b, d):
    """Maximal b-adic nodes contained in [l,u] (iterative, O(b*d))."""
    if l > u:
        return []
    res = []
    stack = [(0, 0)]
    while stack:
        t, p = stack.pop()
        lo, hi = node_range(t, p, b, d)
        if hi < l or lo > u:
            continue
        if l <= lo and hi <= u:
            res.append((t, p))
            continue
        for c in range(b - 1, -1, -1):
            stack.append((t + 1, p * b + c))
    return res

def merge_intervals(ivs):
    ivs = sorted(ivs)
    out = []
    for l, u in ivs:
        if l > u:
            continue
        if out and l <= out[-1][1] + 1:
            if u > out[-1][1]:
                out[-1] = (out[-1][0], u)
        else:
            out.append((l, u))
    return tuple(out)

def intersect_sets(A, B):
    i = j = 0
    out = []
    while i < len(A) and j < len(B):
        l = max(A[i][0], B[j][0]); u = min(A[i][1], B[j][1])
        if l <= u:
            out.append((l, u))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return merge_intervals(out)

def union_sets(A, B):
    return merge_intervals(list(A) + list(B))

def complement_set(A, N):
    out = []
    prev = 0
    for l, u in A:
        if l > prev:
            out.append((prev, l - 1))
        prev = u + 1
    if prev <= N - 1:
        out.append((prev, N - 1))
    return tuple(out)

def cover_set(A, b, d):
    res = []
    for l, u in A:
        res.extend(cover_interval(l, u, b, d))
    return res

def in_set(v, A):
    for l, u in A:
        if l <= v <= u:
            return True
    return False

def set_size(A):
    return sum(u - l + 1 for l, u in A)

def digits_needed(nbits, beta):
    return -(-nbits // beta)

def cover_bound(b, d):
    """Proved worst-case size of the cover of one interval (Lemma 'cover size')."""
    if d == 1:
        return b - 1 if b > 2 else 1
    return (b - 2) + 2 * (b - 1) * (d - 1)

# SCOPE: Subtree Covers over Policy Expressions

Reference implementation and experiment code for the article *SCOPE: Subtree Covers over Policy
Expressions for Adaptively Secure ABE* (Khaled Riad, King Faisal University).

SCOPE compiles Boolean policies (AND, OR, NOT) over integer interval and set predicates into plain
monotone formulas for a large-universe attribute-based encryption (ABE) scheme, using b-adic subtree
covers. The repository holds the compiler, three baseline encodings, an independent semantic oracle,
a pure-Python BN254 pairing with a BSW07-style CP-ABE prototype, and the scripts that produced the
numbers in the paper.

> The pairing prototype is a calibration instrument. It is not constant-time, not hardened, runs on
> BN254 (below 128-bit security) and is **not** adaptively secure. Do not use it to protect data.

## Layout

| Path | Content |
|---|---|
| `scope/covers.py` | b-adic covers, interval-set algebra, the tight size bound `cover_bound` |
| `scope/policy.py` | policy language, oracle, NNF, normalization, cover and bit-wise compilers, random policies |
| `scope/bn254.py`, `scope/abe.py` | BN254 optimal-ate pairing and BSW07-style key encapsulation |
| `experiments.py` | experiments E0-E4 (correctness, widths, random policies, radix, case studies) |
| `bench_proto.py` | pairing prototype measurements used for the cost model (E5) |
| `results/` | `compiler_results.json`, `proto_results.json` |
| `tests/` | exhaustive checks of the cover lemmas and randomized end-to-end checks |

## Quick start

Python 3.9 or newer, standard library only.

```bash
make test          # about one second
make experiments   # regenerates results/compiler_results.json
make prototype     # regenerates results/proto_results.json (slow)
```

```python
from scope.policy import Schema, leaf, compile_cover, rows, key_labelset, eval_labels
sch = Schema([16], beta=1)                      # one 16-bit attribute, binary tree
f = ('AND', [leaf(0, [(100, 5000)]), ('NOT', leaf(0, [(300, 399)]))])
tree = compile_cover(f, sch)
print(rows(tree))                               # number of rows after normalization and cover
print(eval_labels(tree, key_labelset({0: 250}, sch)))   # True
```

## Reproducibility

All random choices use fixed seeds. Re-running `experiments.py` reproduces every row count,
multiplicity, decryption-set size and correctness figure exactly; only the wall-clock columns
(`*_ms`) vary with the machine. The shipped `results/` files were produced on a 2.3 GHz virtual machine.

## Citing

See `CITATION.cff`. Archive DOI: [I will set it later].

## License

MIT, see `LICENSE`.

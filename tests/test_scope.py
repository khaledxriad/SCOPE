"""Exhaustive and randomized checks of the SCOPE compiler (run: python -m unittest discover -s tests)."""
import os, sys, random, unittest
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from scope.covers import cover_interval, key_path, node_range, cover_bound, complement_set
from scope.policy import (Schema, random_policy, compile_cover, compile_bitwise, sem, key_labelset,
                          key_labelset_bitwise, eval_labels, random_assignment, rows)


class CoverLemmas(unittest.TestCase):
    def test_exact_unique_and_tight_bound(self):
        for b in (2, 3, 4):
            for d in (1, 2, 3):
                n = b ** d
                worst = 0
                for l in range(n):
                    for u in range(l, n):
                        cov = cover_interval(l, u, b, d)
                        worst = max(worst, len(cov))
                        for v in range(n):
                            hits = [x for x in key_path(v, b, d) if x in set(cov)]
                            inside = l <= v <= u
                            self.assertEqual(len(hits), 1 if inside else 0)
                self.assertEqual(worst, cover_bound(b, d), (b, d))

    def test_point_complement_cost(self):
        for b, d in ((2, 4), (3, 3), (4, 2)):
            n = b ** d
            for v in (0, n // 2, n - 1):
                cov = sum(len(cover_interval(l, u, b, d)) for l, u in complement_set([(v, v)], n))
                self.assertEqual(cov, (b - 1) * d)


class CompilerCorrectness(unittest.TestCase):
    def test_random_policies_match_oracle(self):
        rng = random.Random(7)
        for _ in range(300):
            sch = Schema([rng.choice([5, 6, 8]) for _ in range(3)], rng.choice([1, 2, 3]))
            f = random_policy(rng.randint(1, 10), sch, rng, p_not_leaf=0.25, p_not_gate=0.1)
            C, C0, B = compile_cover(f, sch, True), compile_cover(f, sch, False), compile_bitwise(f, sch)
            self.assertLessEqual(rows(C), rows(C0))
            for _ in range(20):
                v = random_assignment(sch, rng)
                o = sem(f, v)
                self.assertEqual(eval_labels(C, key_labelset(v, sch)), o)
                self.assertEqual(eval_labels(C0, key_labelset(v, sch)), o)
                self.assertEqual(eval_labels(B, key_labelset_bitwise(v, sch)), o)


class PairingPrototype(unittest.TestCase):
    def test_roundtrip(self):
        from scope.abe import BSW
        from scope.policy import key_labelset as kl
        sch = Schema([4], 1)
        f = ('L', 0, ((3, 9),))
        tree = compile_cover(f, sch)
        abe = BSW(1); abe.setup()
        ct, K = abe.encrypt(tree)
        for v, ok in ((5, True), (12, False)):
            S = kl({0: v}, sch)
            K2 = abe.decrypt(ct, abe.keygen(sorted(S)), S)
            self.assertEqual(K2 == K, ok)


if __name__ == '__main__':
    unittest.main()

"""NIHIL — classical EMULATION of the Fixation Core.
Real closed timelike curves (CTCs) don't exist in our lab, so we find
fixed points the honest way: by brute force and iteration.
Run:  python fixpoint.py
"""

def fixed_points(f, universe):
    """All x with f(x) == x: the 'paradox-free worlds'."""
    return [x for x in universe if f(x) == x]

def deutsch_fixed_distribution(M, iters=5000):
    """Deutsch consistency condition: p = M·p (M is a stochastic matrix).
    Stationary distribution found via damped iteration."""
    n = len(M)
    p = [1.0 / n] * n
    for _ in range(iters):
        q = [sum(M[i][j] * p[j] for j in range(n)) for i in range(n)]
        p = [0.5 * a + 0.5 * b for a, b in zip(p, q)]
    return p

if __name__ == "__main__":
    print("⟁ NIHIL :: Fixation Core (emulation)\n")
    print("NOT-world (grandfather paradox: x -> not x):")
    print("  deterministic fixed points:", fixed_points(lambda x: not x, [False, True]))
    p = deutsch_fixed_distribution([[0, 1], [1, 0]])
    print("  Deutsch-consistent state: P(0)=%.3f  P(1)=%.3f" % tuple(p))
    print("  -> the paradox is resolved by a probabilistic mixture, not a crash.\n")
    print("Identity world (x -> x): every point is allowed:", fixed_points(lambda x: x, range(4)))

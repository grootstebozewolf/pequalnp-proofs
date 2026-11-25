"""Schubert-cell (RREF pivot) partition of Gr(d, pq) for level spaces (Lakshmibai-Brown, Ch. on Schubert cells).
Coordinates are the cells (i, j) in row-major order. Pivot set s_1 < ... < s_d. Basis row b has 1 at s_b,
0 at the other pivots and free coordinates at the non-pivot positions > s_b (cell dim = sum of these counts).
P1 (sum = 0) is linear per basis row: a row with no free position is (e_{s_b}) with sum 1 => cell empty.
Otherwise eliminate the last free coordinate of each row. Remaining unknowns = cell dim - d.
Usage: python schubert.py p q d   -> histogram of unknown counts over non-empty cells."""
import itertools, sys, collections

def cells(p, q, d):
    n = p * q
    for S in itertools.combinations(range(n), d):
        Sset = set(S)
        free = [[c for c in range(s + 1, n) if c not in Sset] for s in S]
        if any(len(f) == 0 for f in free):
            continue                      # P1 kills the cell
        yield S, free, sum(len(f) for f in free) - d

if __name__ == "__main__":
    p, q, d = map(int, sys.argv[1:4])
    from math import comb
    h = collections.Counter(u for _, _, u in cells(p, q, d))
    tot = sum(h.values())
    print(f"{p}x{q} d={d}: {comb(p*q, d)} cells, {comb(p*q, d) - tot} killed by P1, {tot} remain")
    acc = 0
    for u in sorted(h):
        acc += h[u]
        print(f"  unknowns={u:3d}: {h[u]:6d} cells (cumulative {acc})")

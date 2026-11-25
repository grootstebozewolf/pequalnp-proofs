"""Round 5: cell lemmas in echelon-data form (Ech L S v) + top-level assembly; reuses round-4 certificates."""
import itertools, re, json, sys
import sympy as sp
sys.argv = ["x"]
src = open("gen_lean.py").read().replace("\nmain()\n", "\n")
exec(compile(src, "gen_lean.py", "exec"))   # defines cell_data, tmat, perm3, lift, W, pts, mon_expr, X, cells

def P(c): return f"(({c // 3} : Fin 3), ({c % 3} : Fin 3))"
def sub_names(s, S):
    return re.sub(r"a(\d+)_(\d+)", lambda m: f"(v {P(S[int(m.group(1))])} {P(int(m.group(2)))})", s)

out = []
names_all = []
for idx, (S, free, u) in enumerate(cells(3, 3, 4)):
    names, rows = cell_data(S, free)
    E = sp.expand(perm3([[1 + e for e in r] for r in tmat(rows, X)]) - 6)
    poly = sp.Poly(E, *X)
    gens = [g for g in (sp.expand(poly.coeff_monomial(me)) for me in mon_expr) if g != 0]
    consts = [g for g in gens if g.is_number]
    gsel, cof = ([consts[0]], [1 / consts[0]]) if consts else (gens, lift(names, gens))
    Ej = [sp.expand(E.subs(dict(zip(X, pt)))) for pt in pts]
    mu = [0] * len(pts)
    for g, c in zip(gsel, cof):
        mi = next(i for i, me in enumerate(mon_expr) if sp.expand(poly.coeff_monomial(me) - g) == 0)
        for j in range(len(pts)):
            if W[mi, j] != 0: mu[j] += c * W[mi, j]
    mu = [sp.expand(m) for m in mu]
    assert sp.expand(sum(m * e for m, e in zip(mu, Ej)) - 1) == 0
    used = [j for j in range(len(pts)) if mu[j] != 0]
    Sset = set(S)
    L = []
    mem = " ".join(f"(m{c} : {P(c)} {'∈' if c in Sset else '∉'} S)" for c in range(9))
    L.append(f"theorem cell_{idx} (L : Submodule ℂ E) (hL : Level L) (S : Finset (Fin 3 × Fin 3)) (v : Fin 3 × Fin 3 → E)")
    L.append(f"    (hE : Ech L S v) {mem} : False := by")
    facts = []
    for b, s in enumerate(S):
        for c in range(9):
            if c == s:
                L.append(f"  have f{b}_{c} : v {P(s)} {P(c)} = 1 := by rw [hE.2.1 _ m{s} _ m{c}]; exact if_pos rfl")
            elif c in Sset:
                L.append(f"  have f{b}_{c} : v {P(s)} {P(c)} = 0 := by rw [hE.2.1 _ m{s} _ m{c}]; exact if_neg (by decide)")
            elif c < s:
                L.append(f"  have f{b}_{c} : v {P(s)} {P(c)} = 0 := hE.2.2 _ m{s} _ m{c} (by decide)")
            else:
                continue
            facts.append(f"f{b}_{c}")
    hls = []
    for b, s in enumerate(S):
        fr = free[b]
        last = fr[-1]
        rhs = "-1" + "".join(f" - v {P(s)} {P(c)}" for c in fr[:-1])
        L.append(f"  have hs{b} := sum_zero L hL _ (hE.1 _ m{s})")
        L.append(f"  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, {', '.join(x for x in facts if x.startswith(f'f{b}_'))}] at hs{b}")
        L.append(f"  have hl{b} : v {P(s)} {P(last)} = {rhs} := by linear_combination hs{b}")
        hls.append(f"hl{b}")
    memL = " ".join(f"(hE.1 _ m{s})" for s in S)
    for j in used:
        L.append(f"  have h{j} := gen4 L hL _ _ _ _ {memL} {' '.join(f'({x})' for x in pts[j])}")
        L.append(f"  rw [perm3] at h{j}")
        L.append(f"  simp only [Matrix.of_apply, {', '.join(facts + hls)}] at h{j}")
    lc = " + ".join(f"({sub_names(lean_expr(mu[j]), S)}) * h{j}" for j in used)
    L.append(f"  have key : (1 : ℂ) = 0 := by linear_combination {lc}")
    L.append("  exact one_ne_zero key")
    out.append("\n".join(L))
    names_all.append(idx)
    print(idx, flush=True)

glue = open("lean5/Glue.lean").read().replace("\nend PEqualNP.Gct.Scratch219\n", "\n")
top = ["", "/-- Top level (3 × 3, d = 4): no 4-dimensional level space. -/",
       "theorem no_four_dim_level : ¬ ∃ L : Submodule ℂ E, Level L ∧ Module.finrank ℂ L = 4 := by",
       "  rintro ⟨L, hL, h4⟩",
       "  obtain ⟨S, hc, v, hE⟩ := exists_ech L",
       "  rw [h4] at hc",
       "  have hS : S ∈ powersetCard 4 (univ : Finset (Fin 3 × Fin 3)) := mem_powersetCard.2 ⟨subset_univ _, hc⟩",
       "  fin_cases hS <;> first"]
for c in range(9):
    top.append(f"    | exact killed L hL _ v hE {P(c)} (by decide) (by decide)")
for idx in names_all:
    top.append(f"    | exact cell_{idx} L hL _ v hE " + " ".join(["(by decide)"] * 9))
tail = ["", "#print axioms PEqualNP.Gct.Scratch219.no_four_dim_level", "", "end PEqualNP.Gct.Scratch219", ""]
open("lean5/Level3x3d4.lean", "w").write(glue + "\nset_option maxHeartbeats 1000000\n\n" + "\n\n".join(out) + "\n" + "\n".join(top) + "\n" + "\n".join(tail))

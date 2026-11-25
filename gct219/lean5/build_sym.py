import itertools, re
src = open("Level3x3d4.final.lean").read()
src = src.replace("\nset_option maxHeartbeats 1000000\n", "\n")
src = src.replace("\ntheorem cell_", "\nset_option maxHeartbeats 400000 in\ntheorem cell_")
end = "\nend PEqualNP.Gct.Scratch219"
body, _ = src.rsplit(end, 1)
sym = open("sym_section.lean").read()
reps = [0, 5, 7, 10, 15, 20, 37]
reps_S = {0: [0,1,2,3], 5: [0,1,3,4], 7: [0,1,3,6], 10: [0,1,4,6], 15: [0,2,3,4], 20: [0,2,4,6], 37: [1,2,3,6]}
perms = ["1", "Equiv.swap 0 1", "Equiv.swap 0 2", "Equiv.swap 1 2",
         "Equiv.swap 0 1 * Equiv.swap 1 2", "Equiv.swap 1 2 * Equiv.swap 0 1"]
top = ["", "/-- Symmetry route: only the 7 orbit representatives (weight Σ 2^pos) need a cell lemma; every other",
       "pivot set is excluded because some row/column permutation lowers its weight. -/",
       "theorem no_four_dim_level_sym : ¬ ∃ L : Submodule ℂ E, Level L ∧ Module.finrank ℂ L = 4 := by",
       "  rintro ⟨L, hL, h4⟩",
       "  obtain ⟨L', hL', -, S, hc, ⟨v, hE⟩, hmin⟩ := exists_sym L hL",
       "  rw [h4] at hc",
       "  have hS : S ∈ powersetCard 4 (univ : Finset (Fin 3 × Fin 3)) := mem_powersetCard.2 ⟨subset_univ _, hc⟩",
       "  fin_cases hS <;> first"]
for k in reps:
    top.append(f"    | exact cell_{k} L' hL' _ v hE " + " ".join(["(by decide)"] * 9))
for a in perms:
    for b in perms:
        top.append(f"    | exact absurd (hmin ({a}) ({b})) (by decide)")
prints = "\n".join(f"#print axioms PEqualNP.Gct.Scratch219.{t}" for t in
                   ["no_four_dim_level", "level_three_no_four", "finrank_le_three_level", "level_three_le'", "no_four_dim_level_sym"])
# drop old print lines, re-add at end
body = re.sub(r"\n#print axioms [^\n]*", "", body)
fk = open("fk_section.lean").read()
B = {0: "{((0 : Fin 3), (0 : Fin 3)), (0, 1), (0, 2)}", 5: "{((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 0), (1, 1)}", 7: "{((0 : Fin 3), (0 : Fin 3)), (1, 0), (2, 0)}"}
top2 = ["", "/-- Symmetry route with Frobenius–König certificates for the three block cells (single evaluation each)",
        "and lattice certificates only for the remaining four representatives. -/",
        "theorem no_four_dim_level_sym2 : ¬ ∃ L : Submodule ℂ E, Level L ∧ Module.finrank ℂ L = 4 := by"] + top[4:9]
for k in reps:
    if k in B: top2.append(f"    | exact fk_block L' hL' _ v hE {B[k]} (by decide) (by decide)")
    else: top2.append(f"    | exact cell_{k} L' hL' _ v hE " + " ".join(["(by decide)"] * 9))
for a in perms:
    for b in perms:
        top2.append(f"    | exact absurd (hmin ({a}) ({b})) (by decide)")
prints = prints + "\n#print axioms PEqualNP.Gct.Scratch219.no_four_dim_level_sym2"
out = body + "\n" + sym + "\n" + fk + "\n" + "\n".join(top) + "\n" + "\n".join(top2) + "\n\n" + prints + "\n" + end + "\n"
open("Level3x3Sym.lean", "w").write(out)
print(len(out.splitlines()))

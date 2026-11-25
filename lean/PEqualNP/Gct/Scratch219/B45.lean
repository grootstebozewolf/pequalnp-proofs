import PEqualNP.Gct.Scratch219.O45

-- Theorem B for 4 x 5: the dimension bound 6 follows from one emptiness statement per
-- orbit representative cell that the Frobenius-Koenig row argument does not already close.

namespace PEqualNP.Gct.Scratch219.B45

open Finset PEqualNP.Gct.Scratch219.Glue PEqualNP.Gct.Scratch219.O45

-- The pivot set with a given mask.
def dec (m : ℕ) : Finset (Fin 4 × Fin 5) := univ.filter fun x => m.testBit (pos 5 x)

-- A pivot set is empty when no level space has a reduced echelon basis with these pivots.
def CellEmpty (S : Finset (Fin 4 × Fin 5)) : Prop :=
  ∀ (L : Submodule ℂ (Mat 4 5)) (v : Fin 4 × Fin 5 → Mat 4 5), LevelF L → Ech L S v → False

-- The three representatives whose pivots contain matrix row 0.
def fkReps : List ℕ := [127, 1087, 1119]

theorem fk_cells : ∀ m ∈ fkReps, CellEmpty (dec m) := by
  intro m hm L v hL hE
  simp only [fkReps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;>
    exact fk_row L hL (by norm_num) _ v hE 0 (by decide)

theorem theoremB (hcells : ∀ m ∈ reps45, m ∉ fkReps → CellEmpty (dec m))
    (L : Submodule ℂ (Mat 4 5)) (hL : LevelF L) : Module.finrank ℂ L ≤ 6 := by
  have := finrank_lt_of_cells 7 (fun L hL _ S v hc hE hmin => ?_) L hL
  · omega
  have hr := rep45 S hc hmin
  have hS : S = dec (wt2 S) := eq_decode S
  rw [hS] at hE
  by_cases hf : wt2 S ∈ fkReps
  · exact fk_cells _ hf L v hL hE
  · exact hcells _ hr hf L v hL hE

end PEqualNP.Gct.Scratch219.B45

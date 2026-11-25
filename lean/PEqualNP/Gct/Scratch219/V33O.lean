import PEqualNP.Gct.Scratch219.V33
import PEqualNP.Gct.Scratch219.Orbit

-- The 3 x 3 bound with the orbit exclusion done by the bitmask kernel check.

namespace PEqualNP.Gct.Scratch219.V33O

open Finset PEqualNP.Gct.Scratch219.Glue PEqualNP.Gct.Scratch219.V33

def reps33 : List ℕ := [15, 27, 75, 83, 29, 85, 78]

def gl33 : List (List ℕ) := [
    plist (p := 3) (q := 3) (Equiv.swap (0 : Fin 3) 1) (1),
    plist (p := 3) (q := 3) (Equiv.swap (0 : Fin 3) 2) (1),
    plist (p := 3) (q := 3) (Equiv.swap (1 : Fin 3) 2) (1),
    plist (p := 3) (q := 3) (1) (Equiv.swap (0 : Fin 3) 1),
    plist (p := 3) (q := 3) (1) (Equiv.swap (0 : Fin 3) 2),
    plist (p := 3) (q := 3) (1) (Equiv.swap (1 : Fin 3) 2)]

def ex33 : List (ℕ × List ℕ) := [
    (86, plist (p := 3) (q := 3) (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (0 : Fin 3) 1)),
    (92, plist (p := 3) (q := 3) (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2)),
    (228, plist (p := 3) (q := 3) (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (1 : Fin 3) 2))]

theorem check33 : ∀ m ∈ gen 9 4, goodB 9 reps33 gl33 ex33 m = true := by
  decide +kernel

theorem gl33_ok : ∀ l ∈ gl33, ∃ (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm (Fin 3)), l = plist σ τ := by
  intro l hl
  simp only [gl33, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h <;> exact ⟨_, _, h⟩

theorem ex33_ok : ∀ e ∈ ex33, ∃ (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm (Fin 3)), e.2 = plist σ τ := by
  intro e he
  simp only [ex33, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h <;> subst h <;> exact ⟨_, _, rfl⟩

theorem no_four_orbit (L : Submodule ℂ E) (hL : LevelF L) : Module.finrank ℂ L < 4 := by
  refine finrank_lt_of_cells 4 (fun L hL _ S v hc hE hmin => ?_) L hL
  have hr := rep_of_min 4 reps33 gl33 ex33 gl33_ok ex33_ok check33 S hc hmin
  have hL' := level_of_levelF L hL
  have hS := eq_decode S
  simp only [reps33, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h <;> rw [h] at hS <;> subst hS <;> first
    | exact fk_row L hL (by norm_num) _ v hE 0 (by decide)
    | exact cell_5 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact cell_7 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact cell_10 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact cell_15 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact cell_20 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact cell_37 L hL' _ v hE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end PEqualNP.Gct.Scratch219.V33O

#print axioms PEqualNP.Gct.Scratch219.V33O.no_four_orbit

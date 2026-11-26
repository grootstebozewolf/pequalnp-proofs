import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Complex.Basic

/-! Scratch for L-gct-219, case vJ. The cubic `g3` and the chart lemma.

`g3 j x` is `6 e₃` of the four coordinates of `x` other than `j`, written in power sums so
that it matches `G3 j x x x` of L-gct-215 (`cJ`) by `ring`.

`chart`: if `N` linear functionals on `P` vanish together only at `0` and `dim P ≥ 3`, then
three of them, indexed by `C`, map `P` onto `ℂ³`; `y k` (`k ∈ C`) are preimages of the unit
vectors. The certificates in `VJCore` evaluate the cubic conditions at combinations of the
`y k`; the unknowns are the other functionals at the `y k`. -/

namespace PEqualNP.Gct.Scratch219.VJ

open Module Finset

/-- `6 e₃` of the coordinates of `x` other than `j`. -/
def g3 (j : Fin 5) (x : Fin 5 → ℂ) : ℂ :=
  ((∑ l, x l) - x j) * ((∑ l, x l) - x j) * ((∑ l, x l) - x j)
    - 3 * ((∑ l, x l) - x j) * ((∑ l, x l * x l) - x j * x j)
    + 2 * ((∑ l, x l * x l * x l) - x j * x j * x j)

variable {P : Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]

/-- Functionals that vanish together only at `0` span the dual space. -/
theorem finrank_span_eq {N : ℕ} (τ : Fin N → P →ₗ[ℂ] ℂ)
    (inj : ∀ x, (∀ k, τ k x = 0) → x = 0) :
    finrank ℂ (Submodule.span ℂ (Set.range τ)) = finrank ℂ P := by
  set W := Submodule.span ℂ (Set.range τ)
  have h0 : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    exact inj x fun k => hx _ (Submodule.subset_span ⟨k, rfl⟩)
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rwa [h0, finrank_bot, add_zero] at this

omit [FiniteDimensional ℂ P] in
/-- Linearly independent functionals, indexed by a finset, map onto the coordinate space. -/
theorem surj_of_li {N : ℕ} (τ : Fin N → P →ₗ[ℂ] ℂ) (C : Finset (Fin N))
    (li : LinearIndependent ℂ fun k : C => τ k) :
    Function.Surjective (LinearMap.pi fun k : C => τ k) := by
  classical
  rw [← LinearMap.dualMap_injective_iff]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro ψ hψ
  rw [LinearMap.mem_ker] at hψ
  rw [Submodule.mem_bot]
  have hcomb : ∑ k : C, ψ (Pi.single k 1) • τ k = 0 := by
    ext x
    have h := LinearMap.congr_fun hψ x
    rw [LinearMap.dualMap_apply] at h
    have hx : (LinearMap.pi fun k : C => τ k) x = ∑ k : C, τ k x • Pi.single k (1 : ℂ) := by
      ext k'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum] at h
    simpa [LinearMap.sum_apply, map_smul, smul_eq_mul, mul_comm] using h
  have hc := (Fintype.linearIndependent_iff.mp li) _ hcomb
  apply LinearMap.pi_ext
  intro k c
  have : (Pi.single k c : C → ℂ) = c • Pi.single k 1 := by
    ext k'; simp [Pi.single_apply]
  rw [this, map_smul, hc k]
  simp

theorem chart {N : ℕ} (τ : Fin N → P →ₗ[ℂ] ℂ) (inj : ∀ x, (∀ k, τ k x = 0) → x = 0)
    (h : 2 < finrank ℂ P) :
    ∃ C : Finset (Fin N), C.card = 3 ∧ ∃ y : Fin N → P,
      ∀ k ∈ C, ∀ k' ∈ C, τ k' (y k) = if k' = k then 1 else 0 := by
  classical
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range τ)
  have hbfin : b.Finite := (Set.finite_range τ).subset hbsub
  have : Fintype b := hbfin.fintype
  have hcard : b.toFinset.card = finrank ℂ P := by
    rw [← finrank_span_eq τ inj, ← hbspan, finrank_span_set_eq_card hbli]
  -- a preimage under `τ` for every element of `b`
  have pre : ∀ φ : b, ∃ k, τ k = φ := fun φ => hbsub φ.2
  let f : b → Fin N := fun φ => (pre φ).choose
  have hf : ∀ φ : b, τ (f φ) = φ := fun φ => (pre φ).choose_spec
  let T := (Finset.univ : Finset b).image f
  have hT : T.card = b.toFinset.card := by
    rw [Finset.card_image_of_injective _ fun φ ψ e => Subtype.ext (by
      have := congrArg τ e; rwa [hf, hf] at this)]
    simp
  obtain ⟨C, hCT, hC⟩ := Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
  have memb : ∀ k ∈ C, τ k ∈ b := by
    intro k hk
    obtain ⟨φ, -, rfl⟩ := Finset.mem_image.mp (hCT hk)
    rw [hf φ]; exact φ.2
  have li : LinearIndependent ℂ fun k : C => τ k := by
    have hinj : Function.Injective fun k : C => (⟨τ k, memb k k.2⟩ : b) := by
      intro k k' e
      have e' : τ k = τ k' := congrArg Subtype.val e
      obtain ⟨φ, -, hk⟩ := Finset.mem_image.mp (hCT k.2)
      obtain ⟨ψ, -, hk'⟩ := Finset.mem_image.mp (hCT k'.2)
      apply Subtype.ext
      rw [← hk, ← hk'] at e' ⊢
      rw [hf φ, hf ψ] at e'
      rw [Subtype.ext e']
    exact (hbli.comp _ hinj : _)
  have sj := surj_of_li τ C li
  let y : Fin N → P := fun k =>
    if hk : k ∈ C then (sj (Pi.single ⟨k, hk⟩ 1)).choose else 0
  refine ⟨C, hC, y, fun k hk k' hk' => ?_⟩
  have e := (sj (Pi.single ⟨k, hk⟩ 1)).choose_spec
  have e' := congrFun e ⟨k', hk'⟩
  simp only [LinearMap.pi_apply] at e'
  simp only [y, hk, ↓reduceDIte, e', Pi.single_apply, Subtype.mk.injEq]

end PEqualNP.Gct.Scratch219.VJ

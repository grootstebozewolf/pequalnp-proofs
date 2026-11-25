import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Data.Complex.Basic

-- Generic glue for level spaces in p x q matrices: charts, reduced echelon bases, the
-- row and column symmetry, and the Frobenius-Koenig block argument.

namespace PEqualNP.Gct.Scratch219.Glue

open Finset

variable {p q : ℕ}

abbrev Mat (p q : ℕ) := Fin p × Fin q → ℂ

def pos (q : ℕ) (x : Fin p × Fin q) : ℕ := q * x.1.val + x.2.val

def wt2 (S : Finset (Fin p × Fin q)) : ℕ := ∑ x ∈ S, 2 ^ pos q x

def Inj (L : Submodule ℂ (Mat p q)) (S : Finset (Fin p × Fin q)) : Prop :=
  ∀ t ∈ L, (∀ x ∈ S, t x = 0) → t = 0

def Ech (L : Submodule ℂ (Mat p q)) (S : Finset (Fin p × Fin q)) (v : Fin p × Fin q → Mat p q) :
    Prop :=
  (∀ x ∈ S, v x ∈ L) ∧ (∀ x ∈ S, ∀ y ∈ S, v x y = if x = y then 1 else 0) ∧
    (∀ x ∈ S, ∀ y, y ∉ S → pos q y < pos q x → v x y = 0)

theorem exists_inj (L : Submodule ℂ (Mat p q)) :
    ∃ S, Inj L S ∧ S.card = Module.finrank ℂ L := by
  classical
  have hne : (univ.filter (fun S : Finset (Fin p × Fin q) => Inj L S)).Nonempty :=
    ⟨univ, by
      simp only [mem_filter, mem_univ, true_and]
      exact fun t _ h => funext fun x => h x (mem_univ x)⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image _ Finset.card hne
  simp only [mem_filter, mem_univ, true_and] at hS hmin
  refine ⟨S, hS, le_antisymm ?_ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    let f : S → Module.Dual ℂ L := fun x =>
      (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) x.1).comp L.subtype
    have hnli : ¬ LinearIndependent ℂ f := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Subspace.dual_finrank_eq, Fintype.card_coe] at this
      omega
    rw [Fintype.not_linearIndependent_iff] at hnli
    obtain ⟨g, hg, i, hi⟩ := hnli
    have hinj' : Inj L (S.erase i.1) := by
      intro t ht h0
      apply hS t ht
      have hall : ∀ j : S, j ≠ i → t j.1 = 0 := fun j hj =>
        h0 _ (mem_erase.2 ⟨fun e => hj (Subtype.ext e), j.2⟩)
      have hrel := congrArg (fun φ : Module.Dual ℂ L => φ ⟨t, ht⟩) hg
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        f, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply,
        smul_eq_mul] at hrel
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hall j hj, mul_zero]) (by simp)] at hrel
      have hti : t i.1 = 0 := (mul_eq_zero.1 hrel).resolve_left hi
      intro x hx
      by_cases hxi : x = i.1
      · rw [hxi]; exact hti
      · exact h0 x (mem_erase.2 ⟨hxi, hx⟩)
    have := hmin _ hinj'
    rw [card_erase_of_mem i.2] at this
    have : 0 < S.card := card_pos.2 ⟨i.1, i.2⟩
    omega
  · let Φ : L →ₗ[ℂ] (S → ℂ) :=
      { toFun := fun x y => x.1 y.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      exact Subtype.ext (hS x.1 x.2 fun y hy => congrFun hx ⟨y, hy⟩)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

theorem ech_of_min (L : Submodule ℂ (Mat p q)) (S : Finset (Fin p × Fin q)) (hSi : Inj L S)
    (hSc : S.card = Module.finrank ℂ L)
    (hmin : ∀ S', Inj L S' → S'.card = Module.finrank ℂ L → wt2 S ≤ wt2 S') :
    ∃ v, Ech L S v := by
  classical
  let Φ : L →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun x y => x.1 y.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hSi x.1 x.2 fun y hy => congrFun hx ⟨y, hy⟩)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hSc])).1 hinj
  choose w hw using fun s : S => hsurj (Pi.single s 1)
  let v : Fin p × Fin q → Mat p q := fun x => if h : x ∈ S then (w ⟨x, h⟩).1 else 0
  have hv : ∀ x (hx : x ∈ S), v x = (w ⟨x, hx⟩).1 := fun x hx => dif_pos hx
  have hpiv : ∀ x ∈ S, ∀ y ∈ S, v x y = if x = y then 1 else 0 := by
    intro x hx y hy
    have := congrFun (hw ⟨x, hx⟩) ⟨y, hy⟩
    rw [hv x hx]
    change (w ⟨x, hx⟩).1 y = _ at this
    rw [this, Pi.single_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg (fun e => hxy (congrArg Subtype.val e).symm), if_neg hxy]
  refine ⟨v, fun x hx => by rw [hv x hx]; exact (w ⟨x, hx⟩).2, hpiv, ?_⟩
  intro x hx y hy hlt
  by_contra hne0
  have hvL : v x ∈ L := by rw [hv x hx]; exact (w ⟨x, hx⟩).2
  have hye : y ∉ S.erase x := fun h => hy (mem_of_mem_erase h)
  have hS'i : Inj L (insert y (S.erase x)) := by
    intro t ht h0
    have hu : t - t x • v x = 0 := by
      apply hSi _ (L.sub_mem ht (L.smul_mem _ hvL))
      intro s hs
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hsx : s = x
      · subst hsx; rw [hpiv s hx s hx, if_pos rfl]; ring
      · rw [h0 s (mem_insert_of_mem (mem_erase.2 ⟨hsx, hs⟩)), hpiv x hx s hs,
          if_neg (Ne.symm hsx)]; ring
    have hty := congrFun hu y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      h0 y (mem_insert_self _ _), zero_sub, neg_eq_zero] at hty
    have htx : t x = 0 := (mul_eq_zero.1 hty).resolve_right hne0
    have : t = t x • v x := sub_eq_zero.1 hu
    rw [this, htx, zero_smul]
  have hcard : (insert y (S.erase x)).card = Module.finrank ℂ L := by
    rw [card_insert_of_notMem hye, card_erase_of_mem hx]
    have : 0 < S.card := card_pos.2 ⟨x, hx⟩
    omega
  have h1 := hmin _ hS'i hcard
  unfold wt2 at h1
  rw [sum_insert hye] at h1
  have h2 := add_sum_erase S (fun z => 2 ^ pos q z) hx
  have h3 : 2 ^ pos q y < 2 ^ pos q x := Nat.pow_lt_pow_right (by norm_num) hlt
  unfold wt2 at *
  omega

def act (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) : Mat p q →ₗ[ℂ] Mat p q where
  toFun t := fun x => t (σ x.1, τ x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem act_injective (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    Function.Injective (act σ τ) := by
  intro t u h
  funext x
  have := congrFun h (σ.symm x.1, τ.symm x.2)
  simpa [act] using this

theorem act_comp (α γ : Equiv.Perm (Fin p)) (β δ : Equiv.Perm (Fin q)) :
    (act α β).comp (act γ δ) = act (γ * α) (δ * β) := by
  ext t x; rfl

theorem finrank_map_act (L : Submodule ℂ (Mat p q)) (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) : Module.finrank ℂ (L.map (act σ τ)) = Module.finrank ℂ L :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (act_injective σ τ) L)).symm

theorem exists_sym (L : Submodule ℂ (Mat p q)) :
    ∃ σ0 : Equiv.Perm (Fin p), ∃ τ0 : Equiv.Perm (Fin q), ∃ S : Finset (Fin p × Fin q),
      S.card = Module.finrank ℂ L ∧ (∃ v, Ech (L.map (act σ0 τ0)) S v) ∧
        ∀ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)),
          wt2 S ≤ wt2 (S.image fun x : Fin p × Fin q => (σ x.1, τ x.2)) := by
  classical
  let P : (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)) × Finset (Fin p × Fin q) → Prop :=
    fun x => Inj (L.map (act x.1.1 x.1.2)) x.2 ∧ x.2.card = Module.finrank ℂ L
  have hne : (univ.filter P).Nonempty := by
    obtain ⟨S, h1, h2⟩ := exists_inj (L.map (act 1 1))
    exact ⟨((1, 1), S), by
      simp only [mem_filter, mem_univ, true_and, P]
      exact ⟨h1, h2.trans (finrank_map_act L 1 1)⟩⟩
  obtain ⟨⟨⟨σ0, τ0⟩, S0⟩, hx, hmin⟩ := exists_min_image _ (fun x => wt2 x.2) hne
  simp only [mem_filter, mem_univ, true_and, P] at hx hmin
  obtain ⟨hSi, hSc⟩ := hx
  refine ⟨σ0, τ0, S0, hSc, ?_, ?_⟩
  · exact ech_of_min _ S0 hSi (hSc.trans (finrank_map_act L σ0 τ0).symm) fun S' hi hc =>
      hmin ⟨⟨σ0, τ0⟩, S'⟩ ⟨hi, hc.trans (finrank_map_act L σ0 τ0)⟩
  · intro σ τ
    have hφ : Function.Injective (fun x : Fin p × Fin q => (σ x.1, τ x.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (σ.injective h.1) (τ.injective h.2)
    apply hmin ⟨⟨σ0 * σ⁻¹, τ0 * τ⁻¹⟩, _⟩
    refine ⟨?_, (card_image_of_injective _ hφ).trans hSc⟩
    intro t ht h0
    rw [← act_comp, Submodule.map_comp] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hu0 : u = 0 := hSi u hu fun x hx => by
      have := h0 (σ x.1, τ x.2) (mem_image_of_mem _ hx)
      simpa [act] using this
    rw [hu0, map_zero]

-- The embedding sum: for p = q it is the permanent.
noncomputable def F (M : Mat p q) : ℂ := ∑ e : Fin p ↪ Fin q, ∏ r, M (r, e r)

def LevelF (L : Submodule ℂ (Mat p q)) : Prop :=
  ∀ t ∈ L, F (fun x => 1 + t x) = F (fun _ : Fin p × Fin q => (1 : ℂ))

theorem F_act (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) (M : Mat p q) :
    F (fun x => M (σ x.1, τ x.2)) = F M := by
  unfold F
  refine Fintype.sum_equiv (Equiv.embeddingCongr σ τ) _ _ (fun e => ?_)
  rw [← Equiv.prod_comp σ (fun r => M (r, (Equiv.embeddingCongr σ τ e) r))]
  simp [Function.Embedding.congr]

theorem level_map (L : Submodule ℂ (Mat p q)) (hL : LevelF L) (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) : LevelF (L.map (act σ τ)) := by
  rintro _ ⟨t, ht, rfl⟩
  have h := hL t ht
  have e : F (fun x => 1 + act σ τ t x) = F (fun x => (fun y => 1 + t y) (σ x.1, τ x.2)) := rfl
  rw [e]
  exact (F_act σ τ (fun y => 1 + t y)).trans h

theorem F_one : F (fun _ : Fin p × Fin q => (1 : ℂ)) = (Fintype.card (Fin p ↪ Fin q) : ℂ) := by
  simp [F]

theorem F_one_ne_zero (hpq : p ≤ q) : F (fun _ : Fin p × Fin q => (1 : ℂ)) ≠ 0 := by
  rw [F_one, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  exact_mod_cast fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.1 h) (by omega)

-- Frobenius-Koenig: a block of pivots met by every embedding forces F (J + t) = 0.
theorem fk_block (L : Submodule ℂ (Mat p q)) (hL : LevelF L) (hpq : p ≤ q)
    (S : Finset (Fin p × Fin q)) (v : Fin p × Fin q → Mat p q) (hE : Ech L S v)
    (B : Finset (Fin p × Fin q)) (hB : B ⊆ S)
    (hhit : ∀ e : Fin p ↪ Fin q, ∃ i, (i, e i) ∈ B) : False := by
  classical
  have ht : -(∑ x ∈ B, v x) ∈ L := L.neg_mem (L.sum_mem fun x hx => hE.1 x (hB hx))
  have hone : ∀ y ∈ B, (∑ x ∈ B, v x) y = 1 := by
    intro y hy
    rw [Finset.sum_apply, Finset.sum_eq_single y]
    · rw [hE.2.1 y (hB hy) y (hB hy), if_pos rfl]
    · intro x hx hne
      rw [hE.2.1 x (hB hx) y (hB hy), if_neg hne]
    · intro h; exact absurd hy h
  have h := hL _ ht
  have h0 : F (fun x => 1 + (-(∑ x ∈ B, v x)) x) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨i, hi⟩ := hhit e
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Pi.neg_apply, hone _ hi]
    ring
  exact F_one_ne_zero hpq (h ▸ h0)

-- The case used for rectangular shapes: the pivots contain a whole matrix row.
theorem fk_row (L : Submodule ℂ (Mat p q)) (hL : LevelF L) (hpq : p ≤ q)
    (S : Finset (Fin p × Fin q)) (v : Fin p × Fin q → Mat p q) (hE : Ech L S v)
    (i : Fin p) (hrow : ∀ j : Fin q, (i, j) ∈ S) : False := by
  classical
  exact fk_block L hL hpq S v hE (univ.image fun j : Fin q => (i, j))
    (fun x hx => by
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      exact hrow j)
    (fun e => ⟨i, mem_image.2 ⟨e i, mem_univ _, rfl⟩⟩)

-- Restriction to a submodule of a given dimension.
theorem exists_sub_finrank (L : Submodule ℂ (Mat p q)) (d : ℕ) (h : d ≤ Module.finrank ℂ L) :
    ∃ L' : Submodule ℂ (Mat p q), L' ≤ L ∧ Module.finrank ℂ L' = d := by
  let b := Module.finBasis ℂ L
  let f : Fin d → Mat p q := fun i => (b (Fin.castLE h i) : Mat p q)
  have hli : LinearIndependent ℂ f :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h)).map' L.subtype (Submodule.ker_subtype L)
  refine ⟨Submodule.span ℂ (Set.range f), Submodule.span_le.2 ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩; exact (b _).2
  · rw [finrank_span_eq_card hli]; simp

theorem level_mono (L L' : Submodule ℂ (Mat p q)) (hL : LevelF L) (h : L' ≤ L) : LevelF L' :=
  fun t ht => hL t (h ht)

-- The assembly principle: if no orbit-minimal echelon pivot set of size d survives, then
-- every level space has dimension below d.
theorem finrank_lt_of_cells (d : ℕ)
    (hcells : ∀ (L : Submodule ℂ (Mat p q)), LevelF L → Module.finrank ℂ L = d →
      ∀ (S : Finset (Fin p × Fin q)) (v : Fin p × Fin q → Mat p q), S.card = d → Ech L S v →
        (∀ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)),
          wt2 S ≤ wt2 (S.image fun x : Fin p × Fin q => (σ x.1, τ x.2))) → False)
    (L : Submodule ℂ (Mat p q)) (hL : LevelF L) : Module.finrank ℂ L < d := by
  by_contra hge
  obtain ⟨L1, hle, hd⟩ := exists_sub_finrank L d (by omega)
  have hL1 := level_mono L L1 hL hle
  obtain ⟨σ0, τ0, S, hc, ⟨v, hE⟩, hmin⟩ := exists_sym L1
  exact hcells _ (level_map L1 hL1 σ0 τ0) ((finrank_map_act L1 σ0 τ0).trans hd) S v
    (hc.trans hd) hE hmin

end PEqualNP.Gct.Scratch219.Glue

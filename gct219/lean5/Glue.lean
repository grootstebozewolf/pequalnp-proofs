import Mathlib

namespace PEqualNP.Gct.Scratch219

open Finset

abbrev E := Fin 3 × Fin 3 → ℂ

/-- Row-major position of a matrix cell. -/
def pos (p : Fin 3 × Fin 3) : ℕ := 3 * p.1.val + p.2.val

theorem perm3 (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  simp
  ring

/-- `L` is a level space: the permanent stays `6` on `J + L`. -/
def Level (L : Submodule ℂ E) : Prop :=
  ∀ t ∈ L, (Matrix.of fun i j => 1 + t (i, j)).permanent = 6

/-- Glue (b)/(c): on a level space the entry sum (the linear part `P1`) vanishes. -/
theorem sum_zero (L : Submodule ℂ E) (hL : Level L) (t : E) (ht : t ∈ L) : ∑ q, t q = 0 := by
  have h1 := hL _ ht
  have h2 := hL _ (L.neg_mem ht)
  have h3 := hL _ (L.smul_mem 2 ht)
  have h4 := hL _ (L.smul_mem (-2) ht)
  simp only [perm3, Matrix.of_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  linear_combination (8 * (h1 - h2) - (h3 - h4)) / 24

theorem gen4 (L : Submodule ℂ E) (hL : Level L) (a b c d : E) (ha : a ∈ L) (hb : b ∈ L)
    (hc : c ∈ L) (hd : d ∈ L) (y0 y1 y2 y3 : ℂ) :
    (Matrix.of fun i j => 1 + (y0 * a (i, j) + y1 * b (i, j) + y2 * c (i, j) + y3 * d (i, j))).permanent
      = 6 := by
  have := hL (y0 • a + y1 • b + y2 • c + y3 • d)
    (L.add_mem (L.add_mem (L.add_mem (L.smul_mem y0 ha) (L.smul_mem y1 hb)) (L.smul_mem y2 hc))
      (L.smul_mem y3 hd))
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

/-- `S` is a chart: a vector of `L` vanishing on `S` is zero. -/
def Inj (L : Submodule ℂ E) (S : Finset (Fin 3 × Fin 3)) : Prop :=
  ∀ t ∈ L, (∀ p ∈ S, t p = 0) → t = 0

/-- Reduced echelon data: pivots `S`, rows `v p` (p ∈ S) in `L`, `v p q = δ` on pivots, and `v p` vanishes
at non-pivot positions before `p`. -/
def Ech (L : Submodule ℂ E) (S : Finset (Fin 3 × Fin 3)) (v : Fin 3 × Fin 3 → E) : Prop :=
  (∀ p ∈ S, v p ∈ L) ∧ (∀ p ∈ S, ∀ q ∈ S, v p q = if p = q then 1 else 0) ∧
    (∀ p ∈ S, ∀ q, q ∉ S → pos q < pos p → v p q = 0)

theorem exists_inj (L : Submodule ℂ E) : ∃ S, Inj L S ∧ S.card = Module.finrank ℂ L := by
  classical
  have hne : (univ.filter (fun S : Finset (Fin 3 × Fin 3) => Inj L S)).Nonempty :=
    ⟨univ, by simp only [mem_filter, mem_univ, true_and]; exact fun t _ h => funext fun p => h p (mem_univ p)⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image _ Finset.card hne
  simp only [mem_filter, mem_univ, true_and] at hS hmin
  refine ⟨S, hS, le_antisymm ?_ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    let f : S → Module.Dual ℂ L := fun p => (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) p.1).comp L.subtype
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
      intro p hp
      by_cases hpi : p = i.1
      · rw [hpi]; exact hti
      · exact h0 p (mem_erase.2 ⟨hpi, hp⟩)
    have := hmin _ hinj'
    rw [card_erase_of_mem i.2] at this
    have : 0 < S.card := card_pos.2 ⟨i.1, i.2⟩
    omega
  · let Φ : L →ₗ[ℂ] (S → ℂ) :=
      { toFun := fun x p => x.1 p.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      exact Subtype.ext (hS x.1 x.2 fun p hp => congrFun hx ⟨p, hp⟩)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

theorem exists_ech (L : Submodule ℂ E) :
    ∃ S : Finset (Fin 3 × Fin 3), S.card = Module.finrank ℂ L ∧ ∃ v, Ech L S v := by
  classical
  have hne : (univ.filter (fun S : Finset (Fin 3 × Fin 3) =>
      Inj L S ∧ S.card = Module.finrank ℂ L)).Nonempty := by
    obtain ⟨S, h1, h2⟩ := exists_inj L
    exact ⟨S, by simp [h1, h2]⟩
  obtain ⟨S, hS, hmin⟩ := exists_min_image _ (fun S => ∑ p ∈ S, pos p) hne
  simp only [mem_filter, mem_univ, true_and] at hS hmin
  obtain ⟨hSi, hSc⟩ := hS
  let Φ : L →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun x p => x.1 p.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hSi x.1 x.2 fun p hp => congrFun hx ⟨p, hp⟩)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hSc])).1 hinj
  choose w hw using fun s : S => hsurj (Pi.single s 1)
  let v : Fin 3 × Fin 3 → E := fun p => if h : p ∈ S then (w ⟨p, h⟩).1 else 0
  have hv : ∀ p (hp : p ∈ S), v p = (w ⟨p, hp⟩).1 := fun p hp => dif_pos hp
  have hpiv : ∀ p ∈ S, ∀ q ∈ S, v p q = if p = q then 1 else 0 := by
    intro p hp q hq
    have := congrFun (hw ⟨p, hp⟩) ⟨q, hq⟩
    rw [hv p hp]
    change (w ⟨p, hp⟩).1 q = _ at this
    rw [this, Pi.single_apply]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg (fun e => hpq (congrArg Subtype.val e).symm), if_neg hpq]
  refine ⟨S, hSc, v, fun p hp => by rw [hv p hp]; exact (w ⟨p, hp⟩).2, hpiv, ?_⟩
  intro p hp q hq hlt
  by_contra hne0
  have hvL : v p ∈ L := by rw [hv p hp]; exact (w ⟨p, hp⟩).2
  have hqe : q ∉ S.erase p := fun h => hq (mem_of_mem_erase h)
  have hS'i : Inj L (insert q (S.erase p)) := by
    intro t ht h0
    have hu : t - t p • v p = 0 := by
      apply hSi _ (L.sub_mem ht (L.smul_mem _ hvL))
      intro s hs
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hsp : s = p
      · subst hsp; rw [hpiv s hp s hp, if_pos rfl]; ring
      · rw [h0 s (mem_insert_of_mem (mem_erase.2 ⟨hsp, hs⟩)), hpiv p hp s hs,
          if_neg (Ne.symm hsp)]; ring
    have htq := congrFun hu q
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      h0 q (mem_insert_self _ _), zero_sub, neg_eq_zero] at htq
    have htp : t p = 0 := (mul_eq_zero.1 htq).resolve_right hne0
    have : t = t p • v p := sub_eq_zero.1 hu
    rw [this, htp, zero_smul]
  have hcard : (insert q (S.erase p)).card = Module.finrank ℂ L := by
    rw [card_insert_of_notMem hqe, card_erase_of_mem hp]
    have : 0 < S.card := card_pos.2 ⟨p, hp⟩
    omega
  have h1 := hmin _ ⟨hS'i, hcard⟩
  rw [sum_insert hqe] at h1
  have h2 := add_sum_erase S pos hp
  omega

/-- Glue (b): a pivot with no free position after it is impossible (its row would be `e_p`, entry sum 1). -/
theorem killed (L : Submodule ℂ E) (hL : Level L) (S : Finset (Fin 3 × Fin 3)) (v : Fin 3 × Fin 3 → E)
    (hE : Ech L S v) (p : Fin 3 × Fin 3) (hp : p ∈ S) (hfree : ∀ q, q ∉ S → pos q < pos p) : False := by
  have hs := sum_zero L hL (v p) (hE.1 p hp)
  have hvp : v p = Pi.single p 1 := by
    funext q
    by_cases hq : q ∈ S
    · rw [hE.2.1 p hp q hq, Pi.single_apply]
      by_cases e : q = p
      · subst e; simp
      · rw [if_neg (Ne.symm e), if_neg e]
    · rw [hE.2.2 p hp q hq (hfree q hq), Pi.single_apply, if_neg (fun (e : q = p) => hq (e ▸ hp))]
  rw [hvp] at hs
  simp at hs

end PEqualNP.Gct.Scratch219

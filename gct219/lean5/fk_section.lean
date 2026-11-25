
/-- Frobenius–König certificate (one evaluation, no lattice points): if the pivot set contains a set `B`
met by every permutation, then `t = -(Σ_{p ∈ B} v p) ∈ L` has `J + t` vanishing on `B`, so the permanent is `0 ≠ 6`. -/
theorem fk_block (L : Submodule ℂ E) (hL : Level L) (S : Finset (Fin 3 × Fin 3)) (v : Fin 3 × Fin 3 → E)
    (hE : Ech L S v) (B : Finset (Fin 3 × Fin 3)) (hB : B ⊆ S)
    (hhit : ∀ σ : Equiv.Perm (Fin 3), ∃ i, (σ i, i) ∈ B) : False := by
  classical
  have ht : -(∑ p ∈ B, v p) ∈ L := L.neg_mem (L.sum_mem fun p hp => hE.1 p (hB hp))
  have hone : ∀ p' ∈ B, (∑ p ∈ B, v p) p' = 1 := by
    intro p' hp'
    rw [Finset.sum_apply, Finset.sum_eq_single p']
    · rw [hE.2.1 p' (hB hp') p' (hB hp'), if_pos rfl]
    · intro p hp hne
      rw [hE.2.1 p (hB hp) p' (hB hp'), if_neg hne]
    · intro h; exact absurd hp' h
  have h := hL _ ht
  rw [Matrix.permanent, Finset.sum_eq_zero] at h
  · norm_num at h
  · intro σ _
    obtain ⟨i, hi⟩ := hhit σ
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Matrix.of_apply, Pi.neg_apply, hone _ hi]
    ring


/-! ## Round 6: corollary `≤ 3`, and the symmetry route (orbit representatives under the weight `Σ 2^pos`). -/

/-- Corollary: a level space has dimension at most three. -/
theorem finrank_le_three_level (L : Submodule ℂ E) (hL : Level L) : Module.finrank ℂ L ≤ 3 := by
  by_contra hlt
  have h : 4 ≤ Module.finrank ℂ L := by omega
  let b := Module.finBasis ℂ L
  let f : Fin 4 → E := fun i => (b (Fin.castLE h i) : E)
  have hli : LinearIndependent ℂ f :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h)).map' L.subtype (Submodule.ker_subtype L)
  have hr : Module.finrank ℂ (Submodule.span ℂ (Set.range f)) = 4 := by
    rw [finrank_span_eq_card hli]; simp
  have hle : Submodule.span ℂ (Set.range f) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (b _).2)
  exact no_four_dim_level ⟨_, fun t ht => hL t (hle ht), hr⟩

/-- Repo statement style (compare `LevelThree.level_three_le`). -/
theorem level_three_le' (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) :
    Module.finrank ℂ L ≤ 3 :=
  finrank_le_three_level L fun t ht => by
    have := h t ht
    rwa [PEqualNP.Gct.MethodCeiling.eval_permPoly] at this

/-- Tie-free weight of a pivot set. -/
def wt2 (S : Finset (Fin 3 × Fin 3)) : ℕ := ∑ p ∈ S, 2 ^ pos p

theorem ech_of_min (L : Submodule ℂ E) (S : Finset (Fin 3 × Fin 3)) (hSi : Inj L S)
    (hSc : S.card = Module.finrank ℂ L)
    (hmin : ∀ S', Inj L S' → S'.card = Module.finrank ℂ L → wt2 S ≤ wt2 S') : ∃ v, Ech L S v := by
  classical
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
  refine ⟨v, fun p hp => by rw [hv p hp]; exact (w ⟨p, hp⟩).2, hpiv, ?_⟩
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
  have h1 := hmin _ hS'i hcard
  unfold wt2 at h1
  rw [sum_insert hqe] at h1
  have h2 := add_sum_erase S (fun p => 2 ^ pos p) hp
  have h3 : 2 ^ pos q < 2 ^ pos p := Nat.pow_lt_pow_right (by norm_num) hlt
  unfold wt2 at *
  omega

/-- Row/column permutation acting on matrices. -/
def act (σ τ : Equiv.Perm (Fin 3)) : E →ₗ[ℂ] E where
  toFun t := fun p => t (σ p.1, τ p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem act_injective (σ τ : Equiv.Perm (Fin 3)) : Function.Injective (act σ τ) := by
  intro t u h
  funext p
  have := congrFun h (σ.symm p.1, τ.symm p.2)
  simpa [act] using this

theorem act_comp (α β γ δ : Equiv.Perm (Fin 3)) :
    (act α β).comp (act γ δ) = act (γ * α) (δ * β) := by
  ext t p; rfl

theorem level_map (L : Submodule ℂ E) (hL : Level L) (σ τ : Equiv.Perm (Fin 3)) :
    Level (L.map (act σ τ)) := by
  rintro _ ⟨t, ht, rfl⟩
  have h := hL t ht
  have e : (Matrix.of fun i j => 1 + act σ τ t (i, j)) =
      ((Matrix.of fun i j => 1 + t (i, j)).submatrix σ id).submatrix id τ := by
    ext i j; rfl
  rw [e, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols, h]

theorem finrank_map_act (L : Submodule ℂ E) (σ τ : Equiv.Perm (Fin 3)) :
    Module.finrank ℂ (L.map (act σ τ)) = Module.finrank ℂ L :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (act_injective σ τ) L)).symm

theorem exists_sym (L : Submodule ℂ E) (hL : Level L) :
    ∃ L' : Submodule ℂ E, Level L' ∧ Module.finrank ℂ L' = Module.finrank ℂ L ∧
      ∃ S : Finset (Fin 3 × Fin 3), S.card = Module.finrank ℂ L ∧ (∃ v, Ech L' S v) ∧
        ∀ σ τ : Equiv.Perm (Fin 3), wt2 S ≤ wt2 (S.image fun p => (σ p.1, τ p.2)) := by
  classical
  let P : (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) × Finset (Fin 3 × Fin 3) → Prop :=
    fun x => Inj (L.map (act x.1.1 x.1.2)) x.2 ∧ x.2.card = Module.finrank ℂ L
  have hne : (univ.filter P).Nonempty := by
    obtain ⟨S, h1, h2⟩ := exists_inj (L.map (act 1 1))
    exact ⟨((1, 1), S), by simp only [mem_filter, mem_univ, true_and, P]; exact ⟨h1, h2.trans (finrank_map_act L 1 1)⟩⟩
  obtain ⟨⟨⟨σ0, τ0⟩, S0⟩, hx, hmin⟩ := exists_min_image _ (fun x => wt2 x.2) hne
  simp only [mem_filter, mem_univ, true_and, P] at hx hmin
  obtain ⟨hSi, hSc⟩ := hx
  refine ⟨L.map (act σ0 τ0), level_map L hL σ0 τ0, finrank_map_act L σ0 τ0, S0, hSc, ?_, ?_⟩
  · exact ech_of_min _ S0 hSi (hSc.trans (finrank_map_act L σ0 τ0).symm) fun S' hi hc =>
      hmin ⟨⟨σ0, τ0⟩, S'⟩ ⟨hi, hc.trans (finrank_map_act L σ0 τ0)⟩
  · intro σ τ
    have hφ : Function.Injective (fun p : Fin 3 × Fin 3 => (σ p.1, τ p.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (σ.injective h.1) (τ.injective h.2)
    apply hmin ⟨⟨σ0 * σ⁻¹, τ0 * τ⁻¹⟩, _⟩
    refine ⟨?_, (card_image_of_injective _ hφ).trans hSc⟩
    intro t ht h0
    rw [← act_comp, Submodule.map_comp] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hu0 : u = 0 := hSi u hu fun p hp => by
      have := h0 (σ p.1, τ p.2) (mem_image_of_mem _ hp)
      simpa [act] using this
    rw [hu0, map_zero]

import PEqualNP.Gct.Scratch219.Glue
import Mathlib.Combinatorics.Colex

-- Bitmask form of the orbit-minimality test: masks, the permuted mask, and the list of all
-- masks of d-subsets of range n.

namespace PEqualNP.Gct.Scratch219.Glue

open Finset

variable {p q : ℕ}

theorem pos_lt (x : Fin p × Fin q) : pos q x < p * q := by
  unfold pos
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  nlinarith

theorem pos_div (x : Fin p × Fin q) : pos q x / q = x.1.val := by
  unfold pos
  have h2 := x.2.isLt
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h2, Nat.zero_add]

theorem pos_mod (x : Fin p × Fin q) : pos q x % q = x.2.val := by
  unfold pos
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]

theorem pos_injective : Function.Injective (pos (p := p) q) := by
  intro x y h
  have h1 := pos_div x
  have h2 := pos_mod x
  rw [h] at h1 h2
  exact Prod.ext (Fin.ext (h1.symm.trans (pos_div y))) (Fin.ext (h2.symm.trans (pos_mod y)))

theorem wt2_eq (S : Finset (Fin p × Fin q)) : wt2 S = ∑ k ∈ S.image (pos q), 2 ^ k :=
  (sum_image fun x _ y _ h => pos_injective h).symm

theorem testBit_wt2 (S : Finset (Fin p × Fin q)) (k : ℕ) :
    (wt2 S).testBit k ↔ k ∈ S.image (pos q) := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, wt2_eq, Finset.toFinset_bitIndices_sum_two_pow]

theorem mem_of_testBit (S : Finset (Fin p × Fin q)) (x : Fin p × Fin q) :
    (wt2 S).testBit (pos q x) ↔ x ∈ S := by
  rw [testBit_wt2, mem_image]
  exact ⟨fun ⟨y, hy, h⟩ => pos_injective h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

-- The pivot set is recovered from its mask.
theorem eq_decode (S : Finset (Fin p × Fin q)) :
    S = univ.filter fun x => (wt2 S).testBit (pos q x) := by
  ext x
  simp [mem_of_testBit]

-- Permuted mask, given the permutation of positions as a list.
def actL (N : ℕ) (l : List ℕ) (m : ℕ) : ℕ :=
  ∑ k ∈ range N, if m.testBit k then 2 ^ l.getD k 0 else 0

def plist (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) : List ℕ :=
  (List.range (p * q)).map fun k =>
    if h : k / q < p ∧ k % q < q then pos q (σ ⟨k / q, h.1⟩, τ ⟨k % q, h.2⟩) else 0

theorem plist_getD (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) (x : Fin p × Fin q) :
    (plist σ τ).getD (pos q x) 0 = pos q (σ x.1, τ x.2) := by
  have hx := pos_lt x
  have hd := pos_div x
  have hm := pos_mod x
  rw [List.getD_eq_getElem?_getD, plist, List.getElem?_map, List.getElem?_range hx]
  simp only [Option.map_some, Option.getD_some]
  rw [dif_pos ⟨by rw [hd]; exact x.1.isLt, by rw [hm]; exact x.2.isLt⟩]
  congr 3 <;> apply Fin.ext <;> simp [hd, hm]

theorem actL_eq (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) (S : Finset (Fin p × Fin q)) :
    actL (p * q) (plist σ τ) (wt2 S) = wt2 (S.image fun x => (σ x.1, τ x.2)) := by
  classical
  have hg : Function.Injective (fun x : Fin p × Fin q => (σ x.1, τ x.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.1) (τ.injective h.2)
  unfold actL
  rw [← sum_filter]
  have hf : (range (p * q)).filter (fun k => (wt2 S).testBit k) = S.image (pos q) := by
    ext k
    rw [mem_filter, testBit_wt2, mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨x, -, rfl⟩ := mem_image.1 h
      exact ⟨pos_lt x, h⟩
  rw [hf, sum_image fun x _ y _ h => pos_injective h]
  unfold wt2
  rw [sum_image fun x _ y _ h => hg h]
  exact sum_congr rfl fun x _ => by rw [plist_getD]

-- Masks of all d-subsets of range n.
def gen : ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, d + 1 => gen n (d + 1) ++ (gen n d).map (· + 2 ^ n)

theorem gen_mem : ∀ (n d : ℕ) (T : Finset ℕ), T ⊆ range n → T.card = d →
    (∑ k ∈ T, 2 ^ k) ∈ gen n d := by
  intro n
  induction n with
  | zero =>
    intro d T hT hc
    have : T = ∅ := by
      ext k; simp only [notMem_empty, iff_false]; intro hk; simpa using hT hk
    subst this
    subst hc
    simp [gen]
  | succ n ih =>
    intro d T hT hc
    cases d with
    | zero =>
      rw [card_eq_zero] at hc
      subst hc
      simp [gen]
    | succ d =>
      simp only [gen, List.mem_append, List.mem_map]
      by_cases hn : n ∈ T
      · right
        refine ⟨∑ k ∈ T.erase n, 2 ^ k, ih d _ ?_ ?_, ?_⟩
        · intro k hk
          have h1 := hT (mem_of_mem_erase hk)
          have h2 := ne_of_mem_erase hk
          simp only [mem_range] at h1 ⊢
          omega
        · rw [card_erase_of_mem hn, hc]; rfl
        · rw [← add_sum_erase T (fun k => 2 ^ k) hn, Nat.add_comm]
      · left
        refine ih (d + 1) T ?_ hc
        intro k hk
        have h1 := hT hk
        simp only [mem_range] at h1 ⊢
        have : k ≠ n := fun e => hn (e ▸ hk)
        omega

theorem wt2_mem_gen (S : Finset (Fin p × Fin q)) : wt2 S ∈ gen (p * q) S.card := by
  rw [wt2_eq]
  refine gen_mem _ _ _ ?_ ?_
  · intro k hk
    obtain ⟨x, -, rfl⟩ := mem_image.1 hk
    exact mem_range.2 (pos_lt x)
  · exact card_image_of_injective _ pos_injective

-- Splitting the mask list for chunked kernel checks.
theorem gen_succ_succ (n d : ℕ) :
    gen (n + 1) (d + 1) = gen n (d + 1) ++ (gen n d).map (· + 2 ^ n) := rfl

-- The orbit criterion as a Boolean check: a mask is a representative, or is lowered by one of
-- the listed position permutations, or by the one stored for it in the table of extra witnesses.
def goodB (N : ℕ) (reps : List ℕ) (gl : List (List ℕ)) (extra : List (ℕ × List ℕ)) (m : ℕ) :
    Bool :=
  reps.contains m || gl.any (fun l => decide (actL N l m < m)) ||
    (match extra.lookup m with
      | some l => decide (actL N l m < m)
      | none => false)

theorem rep_of_min (d : ℕ) (reps : List ℕ) (gl : List (List ℕ)) (extra : List (ℕ × List ℕ))
    (hgl : ∀ l ∈ gl, ∃ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)), l = plist σ τ)
    (hex : ∀ e ∈ extra, ∃ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)), e.2 = plist σ τ)
    (hcheck : ∀ m ∈ gen (p * q) d, goodB (p * q) reps gl extra m = true)
    (S : Finset (Fin p × Fin q)) (hc : S.card = d)
    (hmin : ∀ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)),
      wt2 S ≤ wt2 (S.image fun x : Fin p × Fin q => (σ x.1, τ x.2))) :
    wt2 S ∈ reps := by
  have hm := wt2_mem_gen S
  rw [hc] at hm
  have h := hcheck _ hm
  have low : ∀ l : List ℕ, (∃ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)), l = plist σ τ) →
      ¬ actL (p * q) l (wt2 S) < wt2 S := by
    rintro l ⟨σ, τ, rfl⟩ hlt
    rw [actL_eq] at hlt
    exact absurd (hmin σ τ) (not_le.2 hlt)
  unfold goodB at h
  simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, decide_eq_true_eq] at h
  rcases h with (h | ⟨l, hl, hlt⟩) | h
  · exact h
  · exact absurd hlt (low l (hgl l hl))
  · split at h
    · rename_i l hlk
      have hmem : (wt2 S, l) ∈ extra := by
        obtain ⟨l₁, l₂, he, -⟩ := (List.lookup_eq_some_iff).1 hlk
        rw [he]; simp
      exact absurd (by simpa using h) (low l (hex _ hmem))
    · exact absurd h (by simp)

theorem gen_split (f : ℕ → Bool) (n d off : ℕ) (h1 : ∀ m ∈ gen n (d + 1), f (m + off) = true)
    (h2 : ∀ m ∈ gen n d, f (m + (off + 2 ^ n)) = true) :
    ∀ m ∈ gen (n + 1) (d + 1), f (m + off) = true := by
  intro m hm
  rw [gen_succ_succ, List.mem_append, List.mem_map] at hm
  rcases hm with hm | ⟨x, hx, rfl⟩
  · exact h1 m hm
  · have := h2 x hx
    rwa [show x + 2 ^ n + off = x + (off + 2 ^ n) by omega]

theorem plist_ok (gs : List (Equiv.Perm (Fin p) × Equiv.Perm (Fin q))) :
    ∀ l ∈ gs.map (fun g => plist g.1 g.2), ∃ (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)),
      l = plist σ τ := by
  intro l hl
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hl
  exact ⟨g.1, g.2, rfl⟩

theorem plist_ok' (gs : List (ℕ × (Equiv.Perm (Fin p) × Equiv.Perm (Fin q)))) :
    ∀ e ∈ gs.map (fun g => (g.1, plist g.2.1 g.2.2)), ∃ (σ : Equiv.Perm (Fin p))
      (τ : Equiv.Perm (Fin q)), e.2 = plist σ τ := by
  intro e he
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 he
  exact ⟨g.2.1, g.2.2, rfl⟩

end PEqualNP.Gct.Scratch219.Glue

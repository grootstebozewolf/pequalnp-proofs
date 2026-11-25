/-! Chunked orbit-exclusion witness lemma for 3x3, d = 4 (r9/gen_chunks.py). Core Lean only. -/
set_option maxRecDepth 100000
namespace WC334
def q : Nat := 3
def rowPerms : List (List Nat) := [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
def colPerms : List (List Nat) := [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
def act (σ τ : List Nat) (m : Nat) : Nat :=
  (List.range 9).foldl (fun acc c => if m.testBit c then acc + 2 ^ (σ.getD (c / q) 0 * q + τ.getD (c % q) 0) else acc) 0
def subsets : Nat → Nat → List Nat
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, k + 1 => (subsets n (k + 1)) ++ ((subsets n k).map (· + 2 ^ n))
def reps : List Nat := [15,27,29,75,78,83,85]
/-- the property: m is a listed orbit representative, or some (σ, τ) in S_3 × S_3 strictly lowers ω -/
def Good (m : Nat) : Prop := m ∈ reps ∨ ∃ i j, act (rowPerms.getD i []) (colPerms.getD j []) m < m
def okH (h m : Nat) : Bool := (h == 36 && reps.contains m) || decide (act (rowPerms.getD (h / 6) []) (colPerms.getD (h % 6) []) m < m)
def chk : List Nat → List Nat → Bool
  | [], [] => true
  | m :: ms, h :: hs => okH h m && chk ms hs
  | _, _ => false
theorem good_of_chk : ∀ (ms hs : List Nat), chk ms hs = true → ∀ m ∈ ms, Good m
  | [], [], _, m, hm => by simp at hm
  | m :: ms, h :: hs, H, x, hx => by
    simp only [chk, Bool.and_eq_true] at H
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [okH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at H
      rcases H.1 with ⟨-, h2⟩ | h2
      · exact Or.inl h2
      · exact Or.inr ⟨_, _, h2⟩
    · exact good_of_chk ms hs H.2 x hx
  | [], _ :: _, H, _, _ => by simp [chk] at H
  | _ :: _, [], H, _, _ => by simp [chk] at H
theorem mem_subsets_succ (n k m : Nat) : m ∈ subsets (n + 1) (k + 1) ↔ m ∈ subsets n (k + 1) ∨ ∃ a ∈ subsets n k, a + 2 ^ n = m := by
  simp [subsets]

def d_3_2 : List Nat := [36]
theorem c_3_2 : chk ((subsets 2 2).map (· + 2 ^ 3 + 2 ^ 2)) d_3_2 = true := by decide +kernel
def d_4_2 : List Nat := [2]
theorem c_4_2 : chk ((subsets 2 2).map (· + 2 ^ 4 + 2 ^ 2)) d_4_2 = true := by decide +kernel
def d_4_3 : List Nat := [36,36,2]
theorem c_4_3 : chk ((subsets 3 2).map (· + 2 ^ 4 + 2 ^ 3)) d_4_3 = true := by decide +kernel
def d_5_2 : List Nat := [3]
theorem c_5_2 : chk ((subsets 2 2).map (· + 2 ^ 5 + 2 ^ 2)) d_5_2 = true := by decide +kernel
def d_5_3 : List Nat := [1,1,3]
theorem c_5_3 : chk ((subsets 3 2).map (· + 2 ^ 5 + 2 ^ 3)) d_5_3 = true := by decide +kernel
def d_5_4 : List Nat := [4,5,4,12,14,15]
theorem c_5_4 : chk ((subsets 4 2).map (· + 2 ^ 5 + 2 ^ 4)) d_5_4 = true := by decide +kernel
def d_6_2 : List Nat := [6]
theorem c_6_2 : chk ((subsets 2 2).map (· + 2 ^ 6 + 2 ^ 2)) d_6_2 = true := by decide +kernel
def d_6_3 : List Nat := [36,1,36]
theorem c_6_3 : chk ((subsets 3 2).map (· + 2 ^ 6 + 2 ^ 3)) d_6_3 = true := by decide +kernel
def d_6_4 : List Nat := [36,36,8,12,12,13]
theorem c_6_4 : chk ((subsets 4 2).map (· + 2 ^ 6 + 2 ^ 4)) d_6_4 = true := by decide +kernel
def d_6_5 : List Nat := [1,1,9,13,12,13,12,26,27,24]
theorem c_6_5 : chk ((subsets 5 2).map (· + 2 ^ 6 + 2 ^ 5)) d_6_5 = true := by decide +kernel
def d_7_2 : List Nat := [8]
theorem c_7_2 : chk ((subsets 2 2).map (· + 2 ^ 7 + 2 ^ 2)) d_7_2 = true := by decide +kernel
def d_7_3 : List Nat := [2,6,2]
theorem c_7_3 : chk ((subsets 3 2).map (· + 2 ^ 7 + 2 ^ 3)) d_7_3 = true := by decide +kernel
def d_7_4 : List Nat := [2,2,4,14,14,16]
theorem c_7_4 : chk ((subsets 4 2).map (· + 2 ^ 7 + 2 ^ 4)) d_7_4 = true := by decide +kernel
def d_7_5 : List Nat := [4,11,4,24,14,29,14,16,16,26]
theorem c_7_5 : chk ((subsets 5 2).map (· + 2 ^ 7 + 2 ^ 5)) d_7_5 = true := by decide +kernel
def d_7_6 : List Nat := [6,6,8,18,18,19,20,20,22,24,31,34,21,24,26]
theorem c_7_6 : chk ((subsets 6 2).map (· + 2 ^ 7 + 2 ^ 6)) d_7_6 = true := by decide +kernel
def d_8_2 : List Nat := [9]
theorem c_8_2 : chk ((subsets 2 2).map (· + 2 ^ 8 + 2 ^ 2)) d_8_2 = true := by decide +kernel
def d_8_3 : List Nat := [7,3,3]
theorem c_8_3 : chk ((subsets 3 2).map (· + 2 ^ 8 + 2 ^ 3)) d_8_3 = true := by decide +kernel
def d_8_4 : List Nat := [10,5,5,25,28,15]
theorem c_8_4 : chk ((subsets 4 2).map (· + 2 ^ 8 + 2 ^ 4)) d_8_4 = true := by decide +kernel
def d_8_5 : List Nat := [3,3,5,15,17,15,15,17,17,27]
theorem c_8_5 : chk ((subsets 5 2).map (· + 2 ^ 8 + 2 ^ 5)) d_8_5 = true := by decide +kernel
def d_8_6 : List Nat := [7,7,9,19,18,19,30,20,35,25,21,23,21,25,27]
theorem c_8_6 : chk ((subsets 6 2).map (· + 2 ^ 8 + 2 ^ 6)) d_8_6 = true := by decide +kernel
def d_8_7 : List Nat := [10,11,10,18,32,33,20,22,22,28,21,23,23,29,28,18,20,21,30,32,33]
theorem c_8_7 : chk ((subsets 7 2).map (· + 2 ^ 8 + 2 ^ 7)) d_8_7 = true := by decide +kernel

/-- every m in subsets N K arises from a top element t < N and a ∈ subsets t (K-1) -/
theorem mem_subsets_top : ∀ (N K m : Nat), m ∈ subsets N (K + 1) → ∃ t < N, ∃ a ∈ subsets t K, a + 2 ^ t = m
  | 0, K, m, h => by simp [subsets] at h
  | N + 1, K, m, h => by
    rcases (mem_subsets_succ N K m).1 h with h | ⟨a, ha, rfl⟩
    · obtain ⟨t, ht, a, ha, e⟩ := mem_subsets_top N K m h; exact ⟨t, by omega, a, ha, e⟩
    · exact ⟨N, by omega, a, ha, rfl⟩
theorem all_good : ∀ m ∈ subsets 9 4, Good m := by
  intro m hm
  obtain ⟨k1, hk1, a, ha, rfl⟩ := mem_subsets_top 9 3 m hm
  obtain ⟨k2, hk2, b, hb, rfl⟩ := mem_subsets_top k1 2 a ha

  rcases (by omega : k1 = 0 ∨ k1 = 1 ∨ k1 = 2 ∨ k1 = 3 ∨ k1 = 4 ∨ k1 = 5 ∨ k1 = 6 ∨ k1 = 7 ∨ k1 = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- k1 = 0
    omega
  · -- k1 = 1
    rcases (by omega : k2 = 0) with rfl
    · simp [subsets] at hb
  · -- k1 = 2
    rcases (by omega : k2 = 0 ∨ k2 = 1) with rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
  · -- k1 = 3
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2) with rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_3_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
  · -- k1 = 4
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2 ∨ k2 = 3) with rfl | rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_4_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_4_3 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
  · -- k1 = 5
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2 ∨ k2 = 3 ∨ k2 = 4) with rfl | rfl | rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_5_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_5_3 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_5_4 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
  · -- k1 = 6
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2 ∨ k2 = 3 ∨ k2 = 4 ∨ k2 = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_6_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_6_3 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_6_4 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_6_5 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
  · -- k1 = 7
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2 ∨ k2 = 3 ∨ k2 = 4 ∨ k2 = 5 ∨ k2 = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_7_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_7_3 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_7_4 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_7_5 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_7_6 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
  · -- k1 = 8
    rcases (by omega : k2 = 0 ∨ k2 = 1 ∨ k2 = 2 ∨ k2 = 3 ∨ k2 = 4 ∨ k2 = 5 ∨ k2 = 6 ∨ k2 = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [subsets] at hb
    · simp [subsets] at hb
    · exact good_of_chk _ _ c_8_2 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_8_3 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_8_4 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_8_5 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_8_6 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
    · exact good_of_chk _ _ c_8_7 _ (List.mem_map.2 ⟨b, hb, by omega⟩)
end WC334
#print axioms WC334.all_good
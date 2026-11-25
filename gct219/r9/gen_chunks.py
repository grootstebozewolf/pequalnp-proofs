"""Task 3: chunked witness lemma for (p,q,d). Masks: bit c <-> cell (c//q, c%q); omega = mask (colex).
Chunk (k1,k2) = d-subsets whose two largest elements are k1 > k2: masks (subsets k2 (d-2)).map (· + 2^k1 + 2^k2).
Each chunk: one `decide +kernel` theorem that every mask is a listed rep or the stored (σ,τ) lowers it.
Assembly: membership lemma for `subsets` reduces ∀ m ∈ subsets n d to the chunks."""
import itertools, sys, json, numpy as np
sys.set_int_max_str_digits(0)
p, q, d = map(int, sys.argv[1:4]); n = p * q
RP = list(itertools.permutations(range(p))); CP = list(itertools.permutations(range(q))); NH = len(RP) * len(CP)
H = np.array([[rp[c // q] * q + cp[c % q] for c in range(n)] for rp in RP for cp in CP], dtype=np.int64)
P2 = (1 << np.arange(n)).astype(np.int64)
def subsets(nn, kk):
    if kk == 0: return [0]
    if nn == 0: return []
    return subsets(nn - 1, kk) + [m + (1 << (nn - 1)) for m in subsets(nn - 1, kk - 1)]
dig = {}; reps = []
for m in subsets(n, d):
    K = [c for c in range(n) if m >> c & 1]; v = P2[H[:, K]].sum(axis=1); k = int(v.argmin())
    if v[k] < m: dig[m] = k
    else: dig[m] = NH; reps.append(m)
L = lambda xs: "[" + ",".join(map(str, xs)) + "]"
out = [f"""/-! Chunked orbit-exclusion witness lemma for {p}x{q}, d = {d} (r9/gen_chunks.py). Core Lean only. -/
set_option maxRecDepth 100000
namespace WC{p}{q}{d}
def q : Nat := {q}
def rowPerms : List (List Nat) := {L([L(r) for r in RP])}
def colPerms : List (List Nat) := {L([L(c) for c in CP])}
def act (σ τ : List Nat) (m : Nat) : Nat :=
  (List.range {n}).foldl (fun acc c => if m.testBit c then acc + 2 ^ (σ.getD (c / q) 0 * q + τ.getD (c % q) 0) else acc) 0
def subsets : Nat → Nat → List Nat
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, k + 1 => (subsets n (k + 1)) ++ ((subsets n k).map (· + 2 ^ n))
def reps : List Nat := {L(reps)}
/-- the property: m is a listed orbit representative, or some (σ, τ) in S_{p} × S_{q} strictly lowers ω -/
def Good (m : Nat) : Prop := m ∈ reps ∨ ∃ i j, act (rowPerms.getD i []) (colPerms.getD j []) m < m
def okH (h m : Nat) : Bool := (h == {NH} && reps.contains m) || decide (act (rowPerms.getD (h / {len(CP)}) []) (colPerms.getD (h % {len(CP)}) []) m < m)
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
"""]
names = []
for k1 in range(d - 1, n):
    for k2 in range(d - 2, k1):
        ms = [m + (1 << k1) + (1 << k2) for m in subsets(k2, d - 2)]
        if not ms: continue
        nm = f"c_{k1}_{k2}"; names.append((k1, k2, nm))
        out.append(f"def d_{k1}_{k2} : List Nat := {L([dig[m] for m in ms])}")
        out.append(f"theorem {nm} : chk ((subsets {k2} {d-2}).map (· + 2 ^ {k1} + 2 ^ {k2})) d_{k1}_{k2} = true := by decide +kernel")
# assembly: subsets n d = by top element k1 : (subsets k1 (d-1)).map (+2^k1); subsets k1 (d-1) by top element k2
out.append(f"""
/-- every m in subsets N K arises from a top element t < N and a ∈ subsets t (K-1) -/
theorem mem_subsets_top : ∀ (N K m : Nat), m ∈ subsets N (K + 1) → ∃ t < N, ∃ a ∈ subsets t K, a + 2 ^ t = m
  | 0, K, m, h => by simp [subsets] at h
  | N + 1, K, m, h => by
    rcases (mem_subsets_succ N K m).1 h with h | ⟨a, ha, rfl⟩
    · obtain ⟨t, ht, a, ha, e⟩ := mem_subsets_top N K m h; exact ⟨t, by omega, a, ha, e⟩
    · exact ⟨N, by omega, a, ha, rfl⟩
theorem all_good : ∀ m ∈ subsets {n} {d}, Good m := by
  intro m hm
  obtain ⟨k1, hk1, a, ha, rfl⟩ := mem_subsets_top {n} {d-1} m hm
  obtain ⟨k2, hk2, b, hb, rfl⟩ := mem_subsets_top k1 {d-2} a ha
""")
cn = {(k1, k2): nm for k1, k2, nm in names}
alt = lambda v, N: " ∨ ".join(f"{v} = {i}" for i in range(N))
lines = [f"  rcases (by omega : {alt('k1', n)}) with " + " | ".join(["rfl"] * n)]
for k1 in range(n):
    lines.append(f"  · -- k1 = {k1}")
    if k1 == 0:
        lines.append("    omega"); continue
    lines.append(f"    rcases (by omega : {alt('k2', k1)}) with " + " | ".join(["rfl"] * k1))
    for k2 in range(k1):
        if (k1, k2) in cn:
            lines.append(f"    · exact good_of_chk _ _ {cn[(k1, k2)]} _ (List.mem_map.2 ⟨b, hb, by omega⟩)")
        else:
            lines.append("    · simp [subsets] at hb")
out.append("\n".join(lines))
out.append(f"end WC{p}{q}{d}\n#print axioms WC{p}{q}{d}.all_good")
open(f"r9/WC{p}{q}{d}.lean", "w").write("\n".join(out))
print(f"{p}x{q} d{d}: chunks {len(names)}, reps {len(reps)}, max chunk {max(len(subsets(k2, d-2)) for _, k2, _ in names)}")

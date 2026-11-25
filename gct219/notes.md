# L-gct-219 — RGR log (run of Tue 24 Nov 2026, 06:35–07:30 Europe/Amsterdam)

Goal: no 7-dim linear L ⊆ ℂ^{4×5} with F(t) = Σ_{f:4↪5} ∏(1+t_{i,f(i)}) ≡ 120 on L.
Nothing was claimed or submitted on the desk or GitHub. Numerics are evidence, not proof.

## Context from the repo (upstream main, fetched 07:37 +0200 = 06:37 CET)
- L-gct-215 (Outside, 7559 lines, PR #806): Q1..Q4 vanish on L ⊆ 4×5 ⇒ dim L ≤ 7. L-gct-219 is the
  same with ≤ 6 (plus the easy reduction F ≡ 120 ⇒ P1..P4 vanish).
- L-gct-180: 6-dim witness with every row sum 0. L-gct-208: 4×6 has 7 = p+q-3. This fits the
  pattern "max = p+q-3" (2×q: STwoRow q-1; 3×3: LevelThree 3; 4×4 row-centred: 197/217 give 5).
- Proven helpers: L-gct-156 (3×q level ⇒ ≤ q+1, one more than conjectured), L-gct-157 (row-centred 3×q ⇒ ≤ q-1),
  STwoRow, RealLevel (over ℝ, only degrees ≤ 2, gives p+q-2), Rado (L-gct-171), MincExpansion (square case).

## Red/Green/QEX
| # | Test | Result |
|---|------|--------|
| T1 | Rectangular Minc expansion F = Σ_k (5-k)! P_k (exact sympy) | GREEN |
| T1b | F≡120 on L ⇔ P1..P4 vanish on L (scale t→st) | GREEN (one-line argument) |
| T2 | Two 6-dim witnesses (row 0 + column 0, with the corner given to the row or to the column) satisfy F≡120 exactly | GREEN |
| T3 | Desk hint: on H={P1=0} (19-dim) the P2 form has rank 19 ⇒ isotropic ≤ 9 | GREEN as computed; **QEX for the hint**: degree ≤ 2 can't go below 9 |
| T4 | Witness is not extendable: first-order extension space K(W) (exact) | First version RED: dim K = 7, not 6. Refactored to a second-order test: the unique candidate W+span(v) gives F−120 = −120c²(3c²+8c+6) ≠ 0 ⇒ **GREEN, exact: both witnesses are inclusion-maximal** |
| T5 | Central claim: no 7-dim level space | **QEX**. No exact method fits the budget. Gröbner/Fano on Gr(7,19) means 84 unknowns and ~320 equations of degree ≤ 4. Numerical evidence is below. |
| T5a | Numerical LM search (search.py), 4×5 d=6 (calibration) | 12/80 random starts converge (plus 1/10 earlier); 3×3 d=3: 5/20, d=4: 0/20 |
| T5b | 4×5 d=7 | 0/740 starts; best relative residual 8.7e-2 (no near-solutions) |
| T5c | Calibration 4×6 d=7 (known to exist) | 0/26 ⇒ **the search is NOT calibrated at d=7**. T5b is weak evidence only. |
| T5d | Every found 6-dim solution is maximal (extend_test.py) | 12/12: exactly one first-order extension direction, and it fails at Q2 (O(1) residual). Matches T4. |
| T5e | Solution families (classify2.py) | The 6-dim solutions have many different support/rank patterns, not only row+column. F_6 has many components. |
| T6 | Centred variants, 4×5 (CENTRING=rows/both) | row-centred: d=4 8/20, d=5 1/20, d=6 0/20; doubly centred: d=2 20/20, d=3 0/20 (best 5e-3, inconclusive), d=4 0/20 |

## Refactor done
- esym gradient via e_{k-1}(a\i)=Σ(-a_i)^j e_{k-1-j}(a), one-hot einsum scatter (≈10× speed), gradient self-test (selftest_grad.py).
- Stall detection, incremental progress files, CENTRING switch.
- LM limits are singular (slow linear convergence, ~1e-4 leftovers), so rank/support classification uses tol 1e-2.

## Assessment
- Reduction 219 ⇐ "Q1..Q4 vanish ⇒ dim ≤ 6" + T1b: routine in Lean.
- The bound 6 itself is open research. 215 needed 7.5k lines for 7, and the 6-dim solution set has many components.
- Promising structure: every known 6-dim level space has a 1-dim first-order extension that dies at Q2.
  Row restriction: L ∩ ker(row i) is a 3×5 level space, so dim L ≤ r_i + LS(3,5) with r_i = rank of row i ≤ 4 (Frobenius–König: 1 ∉ π_i(L)).
  Two-row restriction gives dim L ≤ rank π_{ij}(L) + 4 (STwoRow).

## Next Red steps
1. Calibrate the d=7 search: get 4×6 d=7 to succeed, by warm starts near the 208 witness or with deflated Newton, then rerun 4×5 d=7.
2. Formulate the Lean-shaped lemma: "if LS(3,5) ≤ 5 (sharpen L-gct-156 at q=5), then a 7-dim 4×5 level space has all row ranks r_i ≥ 2",
   and test the profiles numerically. Equivalent Red: prove LS(3,5) = 5 (exactly 156's bound minus one).

---
# Round 2 (Tue 24 Nov 2026, 08:00–08:25 Europe/Amsterdam)

## Reading
- **Mignon–Ressayre 2004** (mr.txt). The technique: if f vanishes (or is constant) on y + L, then T_y f kills L and
  T²_y f is isotropic on L. Lemma 3.1: restricting to an affine subspace can't raise the Hessian rank. Prop 3.3: perm_d has a zero
  (J with corner 1−d) where the Hessian has full rank d². Prop 3.8: det_n has Hessian rank ≤ 2n at singular points.
  For us this gives a **single-point** bound dim L ≤ (n−r) + ⌊r/2⌋ on n = dim ker ∇F(y) ≥ 19, which is never below 9.
- **Meshulam 1989** (me.txt). Thm 1: a linear space of symmetric n×n matrices of rank ≤ r has dim ≤ f(n,r) =
  max(C(r+1,2), kn − C(k,2) [+1 if r odd]), k = ⌊r/2⌋. f(20,r) = 0,1,20,21,39 for r = 0..4, so it bounds dim L ≤ 6 only if
  the Hessians on L have rank ≤ 1. Thm 2 (affine spaces of rank ≥ k) is about det-type rank and doesn't apply here.

## Tests
| # | Test | Result |
|---|------|--------|
| R2-1 | hessian_test.py: Hessian of F at y = J and at y = J+t (t in the witness) on ker ∇F(y) | rank 19 on 19 dims everywhere ⇒ bound 9. **QEX**: no base point can beat 9 (n ≥ 19 ⇒ (n−r)+⌊r/2⌋ ≥ 9). Using two base points (a pencil) gives at most 8 by the standard count for two quadrics (not proved here). Only all points of L together carry the full information, and that is the original problem. |
| R2-2 | meshulam_test.py: ranks of Hess P3(t), Hess P4(t), Hess F(J+t) at witness points | 18, 8–12, 20 ⇒ Meshulam bounds 74–210. **QEX**: restricted to L these Hessians are 0 by polarization (no information); on the ambient space ranks ≥ 2 give f ≥ 20. |
| R2-3a | Calibration: warm starts near the L-gct-208 witness (4×6, d=7) | ε = 0: exact; ε = 0.05 and 0.3 converge (verify 6e-9, 9e-10, slow linear convergence); ε = 1.0: 0/8. |
| R2-3b | Weight continuation (Q2 first, then Q3/Q4) | 4×6 d=7 0/1 within the cap; 4×5 d=6 0/8 (plain LM gets ~15%). Worse than plain LM, dropped. |
| R2-3c | 4×5 d=7 warm starts from the 12 maximal 6-dim solutions + their unique first-order direction | 0/24 (best 0.10). Consistent with T5d, but not independent of it. |
| R2-3 verdict | | **QEX**: the d=7 basin is local (radius between 0.3 and 1). Random-start LM does not find the known 4×6 7-dim space, so 0/740 on 4×5 is **not** evidence. A calibrated global method (e.g. homotopy continuation on the chart equations) is needed. |
| R2-4a | exact_35.py: 3×5 dim-5 witness (row 0 + column 0) gives F ≡ 60 | GREEN (exact) |
| R2-4b | 3×5 search: d=5 2/20, d=6 0/80 (best 7e-3) | Consistent with "max = 5", but this search is uncalibrated in the same way ⇒ not evidence of ≤ 5. LS(3,5) ≤ 5 is **QEX** (proved: ≤ 6, L-gct-156). |
| R2-4c | exact_35.py: row restriction F_{4×5}(row i = 0) = 2·F_{3×5} | GREEN (exact). So L ∩ ker π_i is a 3×5 level space and dim L = r_i + dim(L ∩ ker π_i). |
| R2-4d | "LS(3,5) ≤ 5 ⇒ every row rank of a 7-dim 4×5 level space is ≥ 2" | GREEN as an argument (rank–nullity + R2-4c). As a lever it is **weak**: 6-dim solutions already have every row rank ≥ 2 (e.g. ranks [3,2,2,3], classify2.py), so the case r_i ≥ 2 is the generic case, not a residue. "No 7-dim space with all r_i ≥ 2" is then just the original problem ⇒ **QEX**. |

## Assessment after round 2
Neither paper sharpens the bound. Point-wise second-order (Hessian) methods stop at 9 (or 8 with a pencil). The gap 9 → 6 needs
degree 3/4 information used along all of L, which is what L-gct-215 does by hand (≤ 7, 7.5k lines). A Lean proof of ≤ 6 is not
within near reach. The pieces that are cheap in Lean: the reduction F ≡ 120 ⇔ P1..P4 = 0, the row restriction identity, and
maximality of the witnesses.

## Next Red step
Write a calibrated certificate search: a homotopy-continuation or Gröbner computation on the chart equations,
**first on 4×6 d=7** (must find L-gct-208) and on 3×5 d=6 (expected empty). Only if it passes calibration, run 4×5 d=7. A Lean-usable
outcome would be a finite case split (charts × row-rank profiles) with unit-ideal certificates, as LevelThree does for 3×3.

---
# Round 3 (Tue 24 Nov 2026, 08:28–09:50 Europe/Amsterdam): exact Schubert-cell solver

## What was tried
1. **Coordinate charts mod S_p×S_q** (chart_system.py, exact/): few charts, but each one is a big cell
   ((h−d)·d unknowns: 3×3 d4 = 16, 4×5 d7 = 84). Singular std over Q and mod 32003 stalled on most 3×3 charts (>300 s).
   msolve 0.7 (Debian) crashed (free(): invalid next size) on this input. **Dropped.**
2. **Greedy flag search** (greedy.py, numerical): stuck at dim 2 in 3×3 and dim 3 in 3×5 (max is 3 / 5). **Dropped**, uncalibrated.
3. **Random-start LM at 4×6 d7** (G1 numeric retry): 0/116 (best 1.3e-2). Confirms round 2: random LM is useless here.
4. **Schubert cells (RREF pivot sets)** following Lakshmibai–Brown (schubert.py, cell_solve.py): a canonical, finite,
   disjoint partition of Gr(d, pq). Each cell is an affine space; P1 is linear per basis row: a row with no free
   coordinate is a unit vector, so it is killed, and otherwise P1 eliminates one coordinate. Equations = all x-coefficients of P_k(Σ x_b row_b),
   k = 2..p. Singular std over **Q** (exact); unit=1 ⇔ 1 ∈ ideal, i.e. the cell has no level space.
   S_p×S_q does NOT act on one Schubert decomposition (cells depend on the coordinate order), so no symmetry reduction was
   used. Cells were solved smallest first.

## Cell counts (non-empty after P1)
| case | cells | P1-killed | remain | max unknowns |
|---|---|---|---|---|
| 3×3 d4 | 126 | 56 | 70 | 16 |
| 3×5 d6 | 5005 | 2002 | 3003 | 48 |
| 4×5 d7 | 77520 | 27132 | 50388 | 84 |

## Gates
| gate | test | result |
|---|---|---|
| G0 (sanity) | 3×3 d3: finds non-empty cells; 3×3 d4: all 70 cells unit over Q | **PASS**: 20 non-empty cells at d3 (7 timeouts); **all 70 cells unit at d4**. This is a complete exact re-proof of "3×3 level spaces ≤ 3" (LevelThree). |
| G1 | 4×6 d7: Schubert cell of the L-gct-208 witness image (last row + last column), S = (5,11,18,19,20,21,22), 17 unknowns | **PASS**: unit=0, dim 0 (non-empty) |
| G2 | 4×5 d6 witness cell S = (4,9,15..18), 14 unknowns; 3×5 d5 witness cell S = (4,10,11,12,13), 5 unknowns | **PASS**: both non-empty (dim 0) |
| G3 | 3×5 d6: no level space | **PARTIAL PASS**: 1657 cells unit, 0 non-empty, 46 timeouts (30 s); every cell with ≤ 20 unknowns is unit; cells with 26–48 unknowns not reached |

## 4×5 d7 (after the gates)
- Cells with ≤ 30 unknowns: 8572 cells, **8534 unit over Q, 0 non-empty, 38 timeouts (30 s)**. Every cell with ≤ 25 unknowns is unit.
- Cells with 31–40 unknowns: see the final tally (runD) appended below.
- Not reached: 27668 cells with 41–84 unknowns, including the big cell (84).
- Strength: each unit cell is an **exact** statement over Q (std; lift() gives cofactors). Not yet exported or Lean-checked.
  The claim is: no 7-dim level space lies in those cells. It is NOT a proof of L-gct-219: 38+ timeouts and the large cells remain.

## Certificate structure (cert_sample.py)
- In 5 of 6 sampled unit cells (15–25 unknowns) the coefficient ideal already contains a **nonzero constant**: some
  x-coefficient of P_k on the cell is a nonzero rational independent of the cell coordinates. In Lean that is a one-line `norm_num`.
- The 6th cell: 64 generators; the lift cofactor for 1 has 7 terms.
- So Lean-usable certificates exist and look small for small cells. The open problem is the ~28k large cells, plus the size
  of a 50k-case Lean file. A Lean proof would need either symmetry (choose coordinate orders per S4×S5 orbit) or a
  structural lemma that collapses most cells, e.g. "constant coefficient" cells as one lemma about pivot patterns.

## Next Red step
1. Classify which pivot patterns are killed by a constant coefficient (pattern lemma, no Gröbner basis), and how many cells remain.
2. Re-run timeouts with 300 s, then cells with 41–84 unknowns mod p first (screening), Q only for survivors.
3. Prototype the Lean side on 3×3 d4: 70 cells, all unit (G0). Generate cofactors with lift() and check them in Lean (`linear_combination`).
   This tests the whole certificate pipeline end to end on a proved case.

### runD final tally (09:48 CET): 4×5 d7 cells with 31–35 unknowns (stopped at the 28-min cap)
5138 cells: 4904 unit over Q, 234 timeouts (30 s), 0 non-empty.
**Round-3 total for 4×5 d7:** 13710 of 50388 non-empty-after-P1 cells attempted; 13438 unit (exact over Q), 272 timeouts,
0 non-empty. Every cell with ≤ 25 unknowns is unit. Not reached: 36,678 cells (all cells with 36–84 unknowns, and the rest of 35).

## Round 4 (2026-11-24, 09:53–11:12 CET): covering rule, retries and mod-p screen, Lean pipeline on 3×3 d4

### Step 1: covering rule IU (iterated uniformity). rule4.py; checked with cmp_rule.py against const_detect.py
- Setup: in a cell, row_b = e_{s_b} + w_b, with supp w_b ⊆ F_b and Σ w_b = −1 (from P1). For a multiset of k rows (slots), the x-coefficient of P_k equals C/∏mult!, where
  C = Σ_{c_i ∈ {s_i}∪F_i} ∏ val_i(c_i) · [the c_i lie in distinct rows and distinct columns].
- Collapse step: slot i may be replaced by (+1 at s_i, −1 at one r_i ∈ F_i) when, for every choice of cells in the uncollapsed slots, the weighted match function over the collapsed slots is constant on F_i. This works because Σ_{c∈F_i} w_c g = −g. Iterate. If every slot collapses, C is an explicit integer. C ≠ 0 means that coefficient is a nonzero constant, so the cell is empty over Q (and over ℂ).
- Paper proof of soundness: the collapse identity, multilinearity in the slots (still valid when a row repeats), and the scaling argument (F ≡ 120 ⇔ P1..P4 = 0). Status: **QED, sufficient rule**. Greedy order affects completeness only, not soundness.
- Exact agreement with the Singular constant detector:
  - 3×3 d4: 29 = 29.
  - 3×5 d6: 912 = 912 (0 missed, 0 false).
  - 4×5 d7: 360 = 360, plus 3163 NOCONST = not IU, on the 3523 cells the detector reached. The detector run was stopped at 3523 of 50388 because it was too slow.
- Coverage:
  - 3×3 d4: 29 of 70 cells; 41 not covered.
  - 3×5 d6: 912 of 3003; 2091 not covered.
  - 4×5 d7: 14912 of 50388; 35476 not covered. By slot size: k=2: 6724, k=3: 4134, k=4: 4054. Values: C=1: 11888, C=−1: 1235, C=−2: 1789.
- Every IU cell is an exact closure over Q, because C is computed exactly.

### Step 2: retries and mod-p screen
- retry300 (Q, 300 s): 6 cells attempted, all 6 timed out. Stopped after 23 min (no yield).
- Mod 32003 screen of unreached cells not covered by IU (screen.py, smallest first):
  - 3×5: 261 cells. 185 unit mod p, 74 timeouts (60 s), 2 errors from a kill. 0 non-empty.
  - 4×5: 187 cells. 61 unit mod p, 126 timeouts (30 s). 0 non-empty.
- Re-checked over Q, 4 random 3×5 mod-p units: 1 unit over Q (cell 0,3,5,10,11,13; 48 s), 3 timeouts (240 s).
- Tally (tally4.py; plus the 1 qsample cell for 3×5):
  - 3×3 d4: 70/70 empty over Q (29 IU, 41 by Gröbner basis).
  - 3×5 d6: 1992 empty over Q (912 IU), 0 non-empty, 184 mod-p only, 76 timeouts, 751 unreached.
  - 4×5 d7: 21323 empty over Q (14912 IU, 6411 by Gröbner basis only), 0 non-empty, 61 mod-p only, 212 timeouts, 28792 unreached.

### Step 3: Lean pipeline, 3×3 d4 (gen_lean.py → lean/Cells3x3d4.lean)
- Per cell, the certificate is 1 = Σ_j μ_j(a)(perm(J + t(x_j)) − 6) over the 35 simplex-lattice points x_j with |x| ≤ 3. Here μ = (Singular lift cofactors) × (inverse Vandermonde). Each certificate was re-verified in sympy.
- Lean proof per cell: `h` at those points → `rw [perm_bridge]` → `have key : (1:ℂ) = 0 := by linear_combination …` → `exact one_ne_zero key`.
- Build: 70 theorems `PEqualNP.Gct.Scratch219.cell_k`. `lake build` succeeded (built temporarily as PEqualNP/Scratch219, then removed from the checkout; nothing committed).
- `#print axioms`: all 70 depend only on [propext, Classical.choice, Quot.sound]. No sorry, no native_decide, no axiom.
- Glue still missing (QEX):
  - (a) Every 4-dim subspace of ℂ^9 has an RREF basis for some pivot set. Mathlib has no ready lemma for this.
  - (b) A pivot row with no free position gives perm(J + x e_s) = 6 + 2x, so P1 ≠ 0. Easy, not written.
  - (c) From L ⊆ level set to `h` for the cell parametrisation, including the P1 elimination of the last free entry. Routine.

### Next Red
State and prove an RREF-existence lemma for Submodule ℂ (Fin n → ℂ) of finrank d (glue a). Then assemble a top-level 3×3 theorem from the 70 cells. Separately: a stronger rule beyond IU (e.g. constant after one linear substitution), aimed at the 35476 uncovered 4×5 cells.

## Round 5 (2026-11-24, 12:10–13:35 CET)

### A. Lean 3×3 d4 end to end: QED (top-level theorem builds)
- File: lean5/Level3x3d4.lean (generated by gen_lean5.py, plus Glue.lean, plus a postprocess that adds the import of MethodCeiling and the bridge to the repo-style statement).
- Built with `lake build` as PEqualNP/Scratch219, then removed from the checkout (git status clean).
- Top-level theorems:
  - `no_four_dim_level : ¬ ∃ L : Submodule ℂ (Fin 3 × Fin 3 → ℂ), Level L ∧ finrank L = 4`
  - `level_three_no_four (L) (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (permPoly ℂ 3) = 6) : finrank L ≠ 4`
- `#print axioms`: both depend on [propext, Classical.choice, Quot.sound]. No sorry, no native_decide, no axiom.
- The glue (no Gaussian elimination; Plücker-style minimality):
  - `exists_inj`: some chart S with card S = finrank L on which L → ℂ^S is injective (nonzero minor). Proof: take a minimum-card injective S; by duality-dimension, a card that is too large is linearly dependent in L*, so an element can be dropped.
  - `exists_ech`: among such charts, take the one minimising Σ pos (row-major). The rows v_p are the preimages of e_p.
  - Zero pattern by exchange: if v_p(q) ≠ 0 with q ∉ S and pos q < pos p, then S − p + q is a chart of smaller weight.
  - Difference from the brief: the minimised quantity is position weight rather than lex order. Both are "least nonzero Plücker coordinate" arguments. For the cell lemmas only the RREF zero pattern matters.
  - `sum_zero` (P1) and `killed` (a pivot with no later free position gives Σ = 1).
  - `fin_cases` over powersetCard 4, then the 70 cell lemmas in Ech form.

### B. G = S_p × S_q orbit-minimal pivot sets (orbit.py, exact enumeration over all of G)
- Canonical form: replace L by gL with lex-least pivot set. Since p_{hI}(hL) = ±p_I(L), the pivot set I must satisfy I ≤_lex sort(hI) for all h. The extra hypotheses p_{h⁻¹J}(L) = 0 (J <_lex I) are available but not used (dropping them is sound).
- Counts:

| family | C(n,d) | orbit-minimal | not P1-killed |
|---|---|---|---|
| 3×3 d4 | 126 | 7 | 5 |
| 3×5 d6 | 5005 | 26 | 21 |
| 4×5 d7 | 77,520 | 80 | 63 |

  The top cell is orbit-minimal in each case.
- Status of the 63 live 4×5 d7 orbit-minimal cells: see the C table and the final report (tally5_4x5_d7.json).

### C. Coverage by cell dimension (tally5.py). Retract the "27 %" framing.
- Cell counts are dominated by small cells. The hard cells are the large ones; the earlier per-cell percentages do not measure progress.

### D. Top cell (pivots 0..6; 91 coordinates before P1, 84 after)
- Singular std mod 32003: unit in 4 s. Mod 31991: unit in 3 s. Over Q: unit=1, dim=−1 in 4 s (exact Singular computation; no lift certificate exported yet).
- So the generic case is empty over Q by computer algebra. Other large orbit-minimal cells (unknowns 74–81) exhaust memory (> 4 GB per job) both over Q and mod p in this setup.

### Rule LP (step 2 of the old plan; nearly done when it was deprioritised)
- Rule: repeatedly take the degree ≤ 1 elements of the coefficient ideal, std them, and reduce the rest; a constant is a certificate (ideal membership, so sound).
- Coverage beyond IU: 3×3: 52 of 70 cells; 3×5 d6: 785 of the 2091 cells not covered by IU; 4×5 d7: 10,056 of the 35,046 cells run.
- Validation: no hit on any of the 80 known non-empty 3×5 d5 cells. The witness cells for 3×5 d5 and 4×5 d6 come out NOLIN.

### Round 5, late items (12:55–13:22 CET; per the user checklist)
- Orbit counts verified independently: Burnside count, matching the lex-min enumeration (3x3 k4: 7; 3x5 k6: 26; 4x5 k7: 80).
  Every dropped orbit representative is P1-killed: some pivot has no free position after it (always includes the last cell (p-1,q-1)). Lemma `killed` covers this case.
- Minor hypotheses: they were NOT in the earlier Singular ideals. They are now added for degree <= 2 (|K ∩ S| >= d-2) in minors.py.
  Positive control (minors_check.py): the canonical forms of the 3x5 d5 and 4x5 d6 witnesses violate 0 of the 0 and 71 added minors respectively.
- P1 had already been substituted before Groebner: the 'unknowns' counts are after P1 (top cell 91 -> 84).
- 3x5 d6 live orbit-minimal reps: [(0, 1, 2, 3, 4, 5), (0, 1, 2, 3, 5, 6), (0, 1, 2, 3, 5, 9), (0, 1, 2, 3, 5, 10), (0, 1, 2, 3, 5, 11), (0, 1, 2, 5, 6, 7), (0, 1, 2, 5, 6, 8), (0, 1, 2, 5, 6, 10), (0, 1, 2, 5, 6, 12), (0, 1, 2, 5, 6, 13), (0, 1, 2, 5, 8, 9), (0, 1, 2, 5, 8, 10), (0, 1, 2, 5, 8, 11), (0, 1, 2, 5, 8, 13), (0, 1, 2, 8, 9, 13), (0, 1, 5, 6, 10, 11), (0, 1, 5, 6, 10, 12), (0, 1, 5, 6, 12, 13), (0, 1, 5, 7, 10, 13), (0, 1, 5, 7, 11, 12), (0, 1, 5, 7, 11, 13)]
- 4x5 d7 live orbit-minimal reps: [(0, 1, 2, 3, 4, 5, 6), (0, 1, 2, 3, 4, 5, 10), (0, 1, 2, 3, 4, 5, 11), (0, 1, 2, 3, 5, 6, 7), (0, 1, 2, 3, 5, 6, 9), (0, 1, 2, 3, 5, 6, 10), (0, 1, 2, 3, 5, 6, 12), (0, 1, 2, 3, 5, 6, 14), (0, 1, 2, 3, 5, 9, 10), (0, 1, 2, 3, 5, 9, 11), (0, 1, 2, 3, 5, 9, 14), (0, 1, 2, 3, 5, 10, 15), (0, 1, 2, 3, 5, 10, 16), (0, 1, 2, 3, 5, 11, 17), (0, 1, 2, 5, 6, 7, 10), (0, 1, 2, 5, 6, 7, 13), (0, 1, 2, 5, 6, 8, 10), (0, 1, 2, 5, 6, 8, 12), (0, 1, 2, 5, 6, 8, 14), (0, 1, 2, 5, 6, 10, 11), (0, 1, 2, 5, 6, 10, 12), (0, 1, 2, 5, 6, 10, 13), (0, 1, 2, 5, 6, 10, 15), (0, 1, 2, 5, 6, 10, 16), (0, 1, 2, 5, 6, 10, 17), (0, 1, 2, 5, 6, 10, 18), (0, 1, 2, 5, 6, 12, 13), (0, 1, 2, 5, 6, 12, 17), (0, 1, 2, 5, 6, 12, 18), (0, 1, 2, 5, 6, 13, 14), (0, 1, 2, 5, 6, 13, 18), (0, 1, 2, 5, 8, 9, 10), (0, 1, 2, 5, 8, 9, 11), (0, 1, 2, 5, 8, 10, 13), (0, 1, 2, 5, 8, 10, 14), (0, 1, 2, 5, 8, 10, 15), (0, 1, 2, 5, 8, 10, 16), (0, 1, 2, 5, 8, 10, 18), (0, 1, 2, 5, 8, 11, 13), (0, 1, 2, 5, 8, 11, 14), (0, 1, 2, 5, 8, 11, 16), (0, 1, 2, 5, 8, 11, 17), (0, 1, 2, 5, 8, 11, 18), (0, 1, 2, 5, 8, 13, 14), (0, 1, 2, 5, 8, 13, 18), (0, 1, 2, 5, 13, 14, 18), (0, 1, 2, 8, 9, 13, 14), (0, 1, 2, 8, 9, 13, 18), (0, 1, 5, 6, 10, 11, 15), (0, 1, 5, 6, 10, 11, 17), (0, 1, 5, 6, 10, 12, 15), (0, 1, 5, 6, 10, 12, 16), (0, 1, 5, 6, 10, 12, 17), (0, 1, 5, 6, 10, 12, 18), (0, 1, 5, 6, 10, 17, 18), (0, 1, 5, 6, 12, 13, 17), (0, 1, 5, 7, 10, 13, 15), (0, 1, 5, 7, 10, 13, 16), (0, 1, 5, 7, 10, 16, 17), (0, 1, 5, 7, 10, 16, 18), (0, 1, 5, 7, 11, 12, 18), (0, 1, 5, 7, 11, 13, 17), (0, 1, 5, 7, 13, 14, 18)]
3x5 d6 orbit-minimal live cells: 21 {'emptyQ': 2, 'timeout': 8, 'modp+minors': 2, 'emptyQ+minors': 9}
  unknowns 20-29: 5 {'emptyQ+minors': 5}
  unknowns 30-39: 9 {'timeout': 2, 'modp+minors': 2, 'emptyQ+minors': 4, 'emptyQ': 1}
  unknowns 40-49: 7 {'emptyQ': 1, 'timeout': 6}
  top cell: (48, 'emptyQ')
4x5 d7 orbit-minimal live cells: 63 {'emptyQ': 9, 'timeout': 21, 'unreached': 12, 'modp+minors': 1, 'emptyQ+minors': 20}
  unknowns 40-49: 4 {'emptyQ+minors': 3, 'emptyQ': 1}
  unknowns 50-59: 15 {'emptyQ': 4, 'timeout': 4, 'emptyQ+minors': 7}
  unknowns 60-69: 27 {'unreached': 4, 'timeout': 11, 'modp+minors': 1, 'emptyQ+minors': 10, 'emptyQ': 1}
  unknowns 70-79: 14 {'emptyQ': 1, 'timeout': 5, 'unreached': 8}
  unknowns 80-89: 3 {'emptyQ': 2, 'timeout': 1}
  top cell: (84, 'emptyQ')
- Open items: item 5 (several primes / msolve) and item 6 (incremental Krull dimension) were not run, item 7 (symmetry Lean glue) was not started, and L-gct-215 tightening is still to do.

## Round 6 (2026-11-24, from 13:25 CET; the box clock is unreliable, so times are approximate)

### Item 1: top cell of 4×5 d7 (pivots 0..6). Verdict: empty, for a simple reason, verified independently.
- Lift: `r6/top_cert.py` uses labelled generators and gives `r6/cert_4x5_d7_0-1-2-3-4-5-6.json`. Of 317 generators, 120 have nonzero cofactors, and all of those are constants:
  - −1/20 on every P2 coefficient of a monomial in x1..x5,
  - +1/60 on the P3 ones,
  - −1/120 on the P4 ones.
- Meaning: the pivots fill matrix row 0, so t* = row_0 + … + row_4 ∈ L has row 0 equal to (1,…,1) (the other basis rows are 0 at pivots). Then J − t* has a zero row, so F(J − t*) = 0 ≠ 120. Expanding, 120 − 24·P1 + 6·P2 − 2·P3 + P4 = 0 at t*, and P1 = 0 gives exactly the certificate.
- Independent check (`r6/top_verify.py`: sympy, F built from all 120 injections, no Singular, no schubert.py):
  - row 0 of t* is all ones;
  - F(J + s·t*) is 0 at s = −1 and 120 at s = 0;
  - P1(t*) = 0;
  - −P2/20 + P3/60 − P4/120 = 1.
- The "top cell is generic, so a positive control" premise is false: every top cell whose pivots contain a full row (4×5 d6, 4×6 d7, 3×5 d5) is empty for the same reason. Positive controls must use the canonical cells of real witnesses instead (item 2).
- General rule FK (Frobenius–König): if the pivots contain R×C with |R| + |C| ≥ q + 1, the cell is empty. In 4×5 d7 only full rows fit in 7 pivots.

### Item 2: minors positive control: PASS
- Lex generator, deg ≤ 2, at the canonical cells of witnesses:
  - 3×4 d4: 0 minors.
  - 3×5 d5 (row and column witnesses): 0 minors.
  - 4×5 d6 (row and column witnesses): 71 minors, 0 violated; Singular with 12 coordinates free gives not unit.
  - 4×6 d7: 106 minors, 0 violated, not unit.
- Weight (exp) generator `minorsw.py`, the same code as the 4×5 runs, through `r6/wcontrol.py`:
  - 4×5 d6, both witnesses: deg ≤ 2: 60 minors; deg ≤ 3: 240 minors. 0 violated, not unit.
  - 4×6 d7: deg ≤ 3: 580 minors, 0 violated, not unit.
- Bug found and fixed: det strings with a leading "+" were rejected by Singular. It only affected the first weight control, which was rerun.

### Weight criterion (matches the Lean glue)
- Σpos ('lin') has ties: 4×5 d7 gives 608 reps / 573 live.
- Adopted Σ 2^pos ('exp'): no ties, exactly one rep per orbit. Reps: 3×3 d4: 7; 3×5 d6: 26; 3×5 d5: 18; 4×5 d6: 53; 4×5 d7: 80.
- With exp, no rep is P1-killed. Under lin, every dropped rep is P1-killed.
- `r6/lean_crit_check.py` is an independent plain-Python implementation of the Lean predicate `wt2 S ≤ wt2 (S.image (σ,τ))`. It gives sets identical to orbitw for 3×3, 3×5 and 4×5.
- Reps containing a full row (FK): 3 of 80 under exp, 4 of 573 under lin.
- Minors under weight: p_K = 0 whenever min_h ω(hK) < ω(I) (strictly less).
- R6 uses COLEX (ω = 2^pos) throughout, with no switch mid-round. In the minor generator (minorsw.py line 40), a minor is included iff `int(OM[H[:, K]].sum(axis=1).min()) < wI`, where OM = 2^c (line 12) and wI = ω(I) (line 34). mwq.py and wcontrol.py both call this same generator with mode "exp" and deg 3.

### Lean (R6): QED
- File: lean5/Level3x3Sym.lean (built by lean5/build_sym.py from Level3x3d4.final.lean, sym_section.lean and fk_section.lean).
- `lake build` succeeded. The first build took 157 s (the second build's timing was lost). Heartbeats are scoped per cell lemma (`set_option maxHeartbeats 400000 in`).
- The following all have `#print axioms` = [propext, Classical.choice, Quot.sound]:
  - `no_four_dim_level`
  - `level_three_no_four`
  - `finrank_le_three_level` (the ≤ 3 corollary)
  - `level_three_le'` (repo style)
  - `no_four_dim_level_sym` (7 colex reps + exclusion by `decide` over 36 permutations)
  - `no_four_dim_level_sym2` (3 reps via the Frobenius–König `fk_block`, single evaluation; 4 via lattice certificates)
- The checkout was cleaned afterwards.

### 4×5 d7 under colex (80 reps; r6/table6_final.txt)
- Closed over Q: 37 (3 FK, 2 by plain Groebner basis, 32 with deg-3 colex minors).
- Open: 43 (8 mod-p only, 26 timeout/OOM, 9 unreached).
- Krull probe (r6/probe.jsonl): 6 cells probed. None completed stage A within 120 s. 2 of them finished the minors-only std (dim 18 and dim 28). So these are 'stuck at start'.

### R7 first step (not started)
- Compare open cells under lex vs colex, by count and by unknowns.
- Lex in Lean via the weight f(x) = 2^20 − 2^(19−x). Only the lemma `pos q < pos p → f q < f p` changes.
- Lex gives 63 live 4×5 reps and 5 live 3×3 reps; reuse the R5 lex results. Under colex all 80 reps are live.

## Round 7 (24 Nov 2026, 14:40–16:00 CET; colex Σ2^pos as in R6; ulimit -v 4 GB; mod p first)
**Top-cell correction.** The 4×5 d7 top cell is FK-trivial: it has a full matrix row among its pivots, so F(J − t*) = 0. It is not the generic case. The hard core is the mid-size orbit-minimal cells, with roughly 55–81 unknowns.

### Item 1: new generators (r7/gens.py)
- **FK separator.** Take a block B = R×C with |R|+|C| ≥ q+1. Every injection hits B. So if t ∈ L had π_B(t) = 1_B, then F(J + (−t)) = 0 ≠ 120. Hence 1_B ∉ π_B(L). Equivalently, there is a λ_B ∈ ℂ^B with ⟨λ_B, π_B(row_b)⟩ = 0 for all b and Σλ_B = 1. This adds |B| new unknowns per block.
- **Row rank.** rank π_i(L) ≤ q−1 for every matrix row i, written as all q×q minors of the d×q row restriction. This uses no λ. It follows from the full-row separator.
- **POSITIVE CONTROL (r7/control.py): PASS.** On each witness's canonical colex cell:
  - No row-rank minor is violated at the witness: 3×5 d5 0/2; 4×5 d6 0/12 (row and column witnesses give the same cell (0,1,2,3,5,10)); 4×6 d7 0/14.
  - A λ exists for every FK block at the witness: 3×5 d5 28/28 blocks (1×5, 2×4, 3×3); 4×5 d6 4/4 rows; 4×6 d7 4/4 rows.
  - Singular over ℚ, with all generators added and K witness coordinates freed, gives NOT unit:
    - 3×5 d5: K=8, dim 139 (λ included).
    - 4×5 d6: K=12, dim 69.
    - 4×6 d7: K=14, dim 103 (580 colex minors + 29 FK equations + 14 row-rank minors).
  - Extra check: rr generators on all 18 colex 3×5 d5 reps mod p. Several cells stay non-unit: (1,2,5,6,10) dim 0 and (0,2,5,6,10) dim 0. So the generators do not kill every d5 cell, where level spaces exist.

### Item 2: 3×5 d6 under colex (26 reps)
- Not 8 timed-out of 21: that count was the R5 lex set. Under colex, R6 had FK 1, emptyQ 1, timeout 4, unreached 20.
- R7 run 'rr' (colex deg-3 minors + row rank):
  - 18 unit mod 32003.
  - 15 confirmed by std over ℚ; 1 more ((0,2,3,4,5,6)) by std over ℚ.
  - 2 by Singular modStd(J,1) over ℚ (exactness flag; no certificate exported).
- Status: 20/26 closed over ℚ. **6 OPEN**: (0,1,2,5,6,10) 39u, (0,1,2,3,6,10) 41u, (0,1,3,5,6,7) 41u, (0,1,2,3,5,10) 42u, (0,1,2,5,6,7) 42u, (0,1,2,3,5,6) 46u. These hit timeout 240 s or OOM, and also time out with the full-row FK λ variant.
- **LS(3,5)=5 is NOT closed.**
- Attribution: rerunning the 18 without row rank ('m3', deg-3 colex minors only) gives 17/17 tested still unit mod p, at the same speed. So these closures come from the colex minors, which R6 never ran on 3×5. The row-rank generators were not needed.
- Krull data (r7/krull356.log), colex minors + row rank without P_k (stage A): dims 27, 29, 27, 36, 34, 42. Adding P2 times out after 90 s on all 6.

### Item 3: the 8 mod-p-only 4×5 cells
- `lift` over ℚ directly (no reconstruction needed) for 7 of 8, using λ-free generators.
- Every certificate is tiny: 7–31 nonzero cofactors, 7–142 terms, cofactor degree ≤ 2.
- r7/cert_verify.py is an independent sympy check that does not use Singular. For each certificate it:
  - checks Σ μ_j g_j = 1 by exact expansion;
  - re-identifies every g_j, up to a rational scalar, as a hypothesis recomputed from scratch: an x-coefficient of P_k, a colex minor, or a row-rank minor.
- Result: 7/7 identities hold and all generators are identified. They are mostly colex minors of degree 1–2, plus a few P2 or P4 coefficients. No row-rank generator was used. Example: (0,2,4,7,8,11,15) needs only 7 degree-1 colex minors. They kill row 5's free entries, so the last entry equals −1.
- The 8th cell, (1,2,5,7,10,11,15), ran out of memory in `lift` (over ℚ and mod 32003/31991). It was closed by modStd(J,1) over ℚ in 110 s, so there is no certificate for it yet.
- Bonus: (1,2,6,7,11,12,15) was a timeout cell. It became unit mod p under rr, then got a ℚ lift with 18 generators, sympy-verified.

### Item 4: 26 timeout + 9 unreached 4×5 cells (rr, mod 32003, 180 s, 3 jobs)
- See r7/run_4x5_d7_rr_c32003.jsonl. Apart from (1,2,6,7,11,12,15), every cell run so far timed out.
- Krull probe (r7/krull457.log): stage A (colex minors + row rank only) times out within 30 s on 7 of 8. The exception is (2,3,5,6,7,10,11): dim 27.
- Full-row FK λ variant: tried only on 3×5 (no gain); not run on 4×5.

### Item 5: lex vs colex (r7/lexcolex.py)
- See the final report. Lex 'closed' includes 20 cells closed with LEX minors, which were never positive-controlled under lex (held as conditional in R6).

### R7 final (15:57 CET)
- Item 4 batch finished. All 35 cells ran (no 'unreached' left). 34 stayed open: 32 TIMEOUT at 180 s, 2 OOM ((0,1,2,5,6,7,10) and (0,1,2,3,5,6,10)). The one exception, (1,2,6,7,11,12,15), was closed with a ℚ certificate.
- 4×5 d7 colex: 46/80 closed over ℚ, 34 open (55–81 unknowns, Σu = 2314). Table: r7/table7.py → r7/table7_4x5_d7.json. 'Not run' = 2 is a label bug: those 2 are the OOM cells.
- Lex vs colex, by unknowns only (lex closures NOT counted, since they have no positive control and Lean uses colex wt2): lex has 63 reps with Σu = 4026; colex has 80 reps with Σu = 5003. Colex open after R7: 34 cells, Σu = 2314, unknowns 55..81.
- R8 is not started.

## Round 8 (24 Nov 2026, 15:57–17:05 CET; colex; FK-λ and row-rank generators DROPPED; 4 GB cap)
Generators: P_k x-coefficients plus colex minors of degree ≤ 3, unless stated otherwise.

### Positive control at minor degree 4 and 5 (r7/control.py, MDEG=4/5, RR=0): PASS
- 4×5 d6 witness canonical cell (0,1,2,3,5,10), K=12 coordinates freed, over ℚ:
  - degree 4: 450 minors, NOT unit (dim 60);
  - degree 5: 843 minors, NOT unit (dim 60).
- 4×6 d7 witness cell, K=14 freed, degree 4: 1230 minors, NOT unit (dim 91).
- 4×6 d7 at degree 5 was not run.

### Item 1: subset minimisation and certificates
- 8th 4×5 cell (1,2,5,7,10,11,15):
  - The subset M1+P2+M2 (582 generators: degree-1 and degree-2 colex minors plus P2) is already unit mod p, at degBound B=6.
  - `lift` and `liftstd` over that subset run out of memory (4 GB), including with degBound.
  - Greedy block-dropping (each test a degBound-6 std) did not finish its first level in about 20 min, so I killed it.
  - No certificate yet. The status stays emptyQ-trusted (modStd).
- 3×5 cell (0,2,3,5,6,10), one of the two modStd-only cells: unit at B=7. `lift` and `liftstd` run out of memory, and greedy timed out. No certificate.
- What B bounds: Singular `degBound=B` discards every S-polynomial of total degree > B. Under dp, reductions never raise degree. So "unit at B" means 1 lies in the F_p-span of {m·g_j : deg m + deg g_j ≤ B}, i.e. a mod-p Macaulay certificate exists with deg μ_j ≤ B − deg g_j.
  - 8th cell (generators of degree ≤ 2): μ of degree ≤ 4 on the quadratic generators.
  - 3×5 (0,2,3,5,6,10) (generators of degree ≤ 3): μ of degree ≤ 4 on the cubic generators.
  - Failure at a smaller B is NOT a proof that no lower-degree certificate exists (degree falls in the inhomogeneous case).
  - So D ≤ 2 certificates do not appear here. The certificate degree is rising (D ≈ 4).

### Item 2: LP substitution (all linear generators, r8/lp*.jsonl)
- Unknowns after substitution:
  - 4×5 open cells: 33..81. Smallest: (1,2,5,6,10,11,15) 55→33, (0,2,5,6,10,11,15) 56→37, (0,1,5,6,10,11,15) 57→39, (2,3,5,6,7,10,11) 61→41.
  - 3×5 open cells: 39→39, 41→36, 41→34, 42→38, 42→36, 46→46.
- This yields no closure by itself. The reduced count is now the run order.

### Item 3: degree-4 and degree-5 minors
- 3×5 open cells, full std mod p with degree-4 minors: 6/6 TIMEOUT at 150 s.
- Krull dim of stage A (minors only, no P_k, no row rank) for degree 3 → 4 → 5:
  - (0,1,2,5,6,10): 27 → 27 → 27
  - (0,1,2,3,6,10): 29 → 25 → TIMEOUT
  - (0,1,3,5,6,7): 29 → TIMEOUT → TIMEOUT
  - (0,1,2,3,5,10): 38 → 33 → 33
  - (0,1,2,5,6,7): 36 → 30 → 30
  - (0,1,2,3,5,6): 44 → 44 → 42
- For comparison, R7 stage A with row rank gave 27/29/27/36/34/42, so row rank did cut 0–2 dims in stage A.

### Item 4: bounded-degree search and case splits
- degBound std on the 6 open 3×5 cells: no unit up to B=4. B=5 does not finish within 240 s, or runs out of memory.
- Case splits on v = the variable making the most generators constant at v=0:
  - (0,1,2,3,6,10), v=a0_4: v=0 unit mod p (msolve); v≠0 crash/timeout.
  - (0,1,2,5,6,7), v=a0_8: v≠0 unit mod p (Singular 0 s, and msolve); v=0 crash/timeout.
  - (0,1,2,5,6,10), v=a5_11: both branches timeout/crash.
  - (0,1,2,3,5,6), v=a0_4: both branches timeout/crash.
- Incremental Krull by basis rows: not run.

### Item 5: msolve built from source (git HEAD 0ae16f2, 23 Nov 2026), `-g 2 -t 2`, mod p
- Control: the non-empty 3×5 d5 cell (1,2,5,6,10) gives a 52-element GB (NOT unit). Correct.
- Agreement: the R7-closed 3×5 (0,2,3,5,6,10) is unit in msolve in 0.2 s.
- New mod-p units, all confirmed at both p=32003 and p=65521:
  - 3×5: (0,1,3,5,6,7) and (0,1,2,3,5,10). Singular had timed out on both.
  - 4×5: (1,2,5,6,10,11,15), (2,3,5,6,7,10,11) (0.6 s, vs Singular TIMEOUT 180 s), (0,2,3,5,6,11,15), (0,1,3,6,7,10,15), (1,2,3,6,7,10,15), (1,2,3,4,6,7,10), (1,3,4,5,6,7,10).
- Failures: 20 4×5 cells crash or run out of memory at 4 GB; 7 were not reached.
- These are mod p only, so they stay OPEN until a ℚ proof exists. msolve gives no ℚ certificate.
- Benchmark on (2,3,5,6,7,10,11):

| Method | Result |
|---|---|
| msolve | unit in 0.6 s |
| Singular std mod p | TIMEOUT 180 s |
| Singular stage A | dim 27 |
| degBound search | not run on this cell |

### Lean: mask witness table (r8/gen_wtable.py → r8/lean/WT*.lean; core Lean, `decide +kernel`)
- Masks are n-bit (ω = mask value = colex). For each d-subset the file stores one (σ,τ) digit with mask(hI) < mask(I), or a rep marker.
- The checker walks `subsets n d` (increasing by construction) in step with the digit list. It also checks the rep count.
- 3×3 d4: 126 subsets, 7 reps (= orbitw). Builds in about 1.3 s. Axioms: [propext].
- 3×5 d6: 5005 subsets, 26 reps (= orbitw). Builds in 21 s. Axioms: [propext].
- 4×5 d7: table generated (77,520 subsets, 80 reps = orbitw, 358 KB file). The kernel check was killed (exit 137, memory) after about 110 s, twice. Next: split into one theorem per chunk of subsets.
- Not yet linked to the Finset glue (Level3x3Sym). No commits.

### Status (r8/table8.py fixes the table7 label bug: the 2 'not run' cells were OOM)
- 4×5 d7 (80 reps):
  - Closed over ℚ: 45 = 8 with sympy-verified certificates + 34 by exact Singular std over ℚ + 3 FK.
  - emptyQ-trusted (modStd only): 1.
  - Open: 34 = 7 mod-p units (msolve, 2 primes) + 27 with no result.
- 3×5 d6 (26 reps):
  - Closed over ℚ: 18 = exact std over ℚ 16 + FK 1 + R6 1.
  - emptyQ-trusted: 2.
  - Open: 6, of which 2 are mod-p units under msolve.
- LS(3,5)=5 NOT closed.

## Round 9 (24 Nov 2026, from 17:07 CET; colex; 4 GB caps)
Status vocabulary, one per cell: V (explicit μ over ℚ, sympy-expanded, every g_j recomputed independently) > E (exact ℚ Gröbner, incl. FK) > T (modStd multimodular) > M_p (unit mod 2 primes, NOT a proof) > O (open).

### Task 1: certificate extraction (r9/dd.py)
- Method:
  1. Sort generators by (degree, length) and binary-search the shortest unit prefix with msolve.
  2. Run ddmin on that prefix. Each membership test is msolve -g 2 mod 32003, with a 10 s cap; a timeout counts as "not unit", which is the conservative direction.
  3. Lift over ℚ on the support, then run cert_verify.
- Progress when stopped (support size after ~105–125 tests):

| Cell | Generators | Unit prefix | Support so far |
|---|---|---|---|
| (2,3,5,6,7,10,11) | 1621 | 1277 | 198 |
| (1,2,3,4,6,7,10) | 824 | 764 | 260 |
| (1,2,5,6,10,11,15) | 4056 | 4025 | 405 |

- ddmin did not converge within budget, so no ℚ lift was attempted. **No new V.** The other 9 targets were not reached.
- The user's amendment (minors before P_k in the prefix order) was not rerun.
- Lean risk: supports of about 200 generators with cofactors of degree about 4 (B=6–7) are probably too big for `linear_combination`.
- Case-split branches still owed: (0,1,2,3,6,10) a0_4≠0 and (0,1,2,5,6,7) a0_8=0. Not done; both cells stay O.

### Task 2: Theorem A gate (LS(3,5)=5 via K = L ∩ R°)
- **P2|_H formula** P2 = ½(|w|² − q(q−1)|a|² − p(p−1)|b|²): checked exactly in sympy for 3×5 and 4×5 (r9/p2check.py).
- **L-gct-157 check** (pequalnp-proofs/lean/PEqualNP/Gct/L157.lean, `theorem PEqualNP.Gct.L157`, proved via centred_of_rado L171):
  - Hypotheses: L ⊆ (Fin 3 × Fin q → ℂ); every t ∈ L has all row sums 0 and P2(t) = P3(t) = 0, written as explicit matching sums.
  - Conclusion: finrank L + 1 ≤ q.
  - Field ℂ. There is no explicit base point or level value: the level conditions F(J+t) = F(J) = q!/(q−p)! with J = all-ones are equivalent to P1=P2=P3=0 on L by the Minc expansion.
  - It matches Cor 4.2: K = L ∩ R° satisfies these hypotheses, so dim K ≤ 4. Lemma 4.1 gives dim K ≥ 6 − 2. So dim K = 4 and L → V_r is onto.
  - I did not re-run axioms for L157 this round.
- **𝒦 gate** (r9/kgate.py: cells of Gr(4,12) in coordinates f_ij = e_ij − e_i4; level ⇔ x-coefficients of P2, P3 vanish; std mod p):
  - First pass, 225 of 495 cells, in order of size: 123 empty, 18 dim 0, 28 dim 1, 21 dim 2, 12 dim 3, 5 dim 4, 3 dim 5, 15 TIMEOUT.
  - So **dim 𝒦 ≥ 5, and the gate is NOT passed** (𝒦 is not small).
  - The S3×S4 lex-orbit reduction (no extra minors: I ≤ piv(hgK) ≤ sorted(hI)) leaves 11 cells. These are the largest cells, 20–24 unknowns, and they time out at 240 s. Components up to G were not computed.
- **Positive control:**
  - Row witness: L5 ∩ R° = row-0 sum-zero space (dim 4), the origin of the 𝒦-cell (0,1,2,3).
  - Column witness: L5 ∩ R° = span{f01, f02, f03} (dim 3; Lemma 4.1 bound d−2 = 3). Its 3-dim cell (1,2,3) timed out at 200 s.
  - Fibre-system control (r9/fibre.py), with K fixed at the row-witness point:
    - one V_r row (d=5): NOT unit, so the witness L5 is recovered;
    - two V_r rows (d=6): unit (consistent).
- **Fibre systems on the 18 zero-dim 𝒦 cells** (16 σ unknowns + cell params, mod p): 14 unit, meaning no level 6-dim L over these K, mod p only. 4 TIMEOUT at 60 s: (0,2,10,11), (1,8,10,11), (2,4,9,11), (2,5,8,11).
- **No counterexample** (non-empty orbit-minimal cell) found anywhere.

### Task 3: Lean witness lemma (r9/gen_chunks.py → r9/WC*.lean; core Lean, no Mathlib)
- Statement: `all_good : ∀ m ∈ subsets n d, Good m`, where `Good m := m ∈ reps ∨ ∃ i j, act (rowPerms.getD i []) (colPerms.getD j []) m < m`. Masks have ω = colex value.
- Chunked by the two largest elements: one `decide +kernel` theorem per chunk. Assembly uses a proved membership lemma for `subsets` and case analysis by `omega`/`rcases`.

| Case | Chunks | Reps | Build time | Axioms |
|---|---|---|---|---|
| 3×3 d4 | 21 | 7 | ~1 s | [propext, Classical.choice, Quot.sound] |
| 3×5 d6 | 55 | 26 | 25 s | [propext, Classical.choice, Quot.sound] |
| 4×5 d7 | 105 | 80 | 352 s, no memory kill | [propext, Classical.choice, Quot.sound] |

- **Not yet linked** to the Finset glue (wt2 on Finset (Fin p × Fin q)). The missing bridge is mask(S) = wt2 S plus the image lemma.
- The conditional Theorem B (one hypothesis 1 ∈ J_I per open cell) needs a 4×5 glue analogous to Level3x3Sym, which does not exist yet. Only the plan exists; there is no Lean draft.

### Status per cell (r9/status9.py → r9/status9.json)
- 3×5 d6 (26): V 0, E 18 (incl. FK 1), T 2, M_p 2, O 4. LS(3,5)=5 NOT closed.
- 4×5 d7 (80): V 8, E 37 (incl. FK 3), T 1, M_p 7, O 27.

### Claims ledger
| Claim | Level | Where | Notes |
|---|---|---|---|
| 3×3: no 4-dim level space; finrank ≤ 3 | V (Lean Qed) | lean5/Level3x3Sym.lean | axioms propext/choice/Quot.sound |
| 4×5 cells closed with sympy-checked μ (8) | V | r7/cert_*_0.txt, cert_verify.py | |
| 4×5 cells closed by exact ℚ std / FK (37) | E | qorbit, mw_exp deg-3, R6 | Singular output, no exported μ |
| 3×5 cells closed by exact ℚ std / FK (18) | E | r7/run_3x5_d6_rr_c0.jsonl | |
| modStd closures (4×5: 1; 3×5: 2) | T | r7/modstd*.log | |
| msolve units (4×5: 7; 3×5: 2) | M_p | r8/ms_*.out (p=32003, 65521) | not a proof |
| 14/18 zero-dim 𝒦 cells admit no level L | M_p | r9/fibre.jsonl | mod p only |
| dim 𝒦 ≥ 5 | M_p (lower bound) | r9/kgate_k4_c32003.jsonl | gate not passed |
| Witness lemmas WC334/WC356/WC457 | V (Lean, core) | r9/WC*.lean | not linked to glue |
| P2|_H formula (3×5, 4×5) | V (sympy identity) | r9/p2check.py | |
| LS(3,5)=5 | O | | 4 O + 2 M_p + 2 T cells remain |
| "27% of 4×5 cells closed" | SUPERSEDED (R5) | | cell count, not by unknowns; retracted |
| "Top cell = generic case / positive control" | SUPERSEDED (R6/R7) | | top cell is FK-trivial |
| "Lex minors closures" (R5, 20 cells) | SUPERSEDED / not counted | | no lex positive control; Lean uses colex |
| "FK λ separators / row-rank minors cut cells" | SUPERSEDED (R8) | | λ condition open-dense; row rank redundant for closures (0 certs used it) |
| "LP rule closes large cells" | SUPERSEDED | | LP reduces ≤ 23 unknowns, closes none of the open cells |

## Round 10 (go 18:17 CET, [pt402u]) — eliminate σ analytically; change the proof object

### Item 1: A_K and the push-down (3×5, d = 6)
- Set-up (r10/ak.py). For K ∈ 𝒦 ⊂ Gr(4, R°), L = K ⊕ span{v_i + σ_i}, σ_i = Σ_{c∉piv K} s_{i,c} f_c. The σ-linear equations are B(κ_a, v_i+σ_i) = 0 (4) and C(κ_a, κ_b, v_i+σ_i) = 0, a ≤ b (10). So A_K is 14×8, the same matrix for i = 1, 2, and the 16-unknown matrix is A_K ⊕ A_K. "Rank 16" means rank A_K = 8.
- Positive control (row witness, K = row-r sum-zero space, r = 0, 1, 2): rank A_K = 4 (the B-rows have rank 4; the C-rows are identically 0, because two κ's in one row kill every P3 term). The control point is therefore itself a rank-drop point.
- **Generic rank is not 16 on all of 𝒦.** Rank is component-dependent:
  - zero-dim cells, exact over ℚ per minimal prime of I_K (r10/fibprime.py → r10/fibprime_final.jsonl; ranks cross-checked by sympy at the explicit algebraic points in r10/ak_points.json): primes with rank 8, 7, 6 and 5 all occur. Cells (4,9,10,11), (5,8,10,11), (1,8,10,11), (1,6,8,11), (2,5,8,11), (3,5,8,10) have rank 7 only; (6,8,9,11) and (3,6,8,9) rank 6; (7,8,9,10) rank 5. The rest mix 8 and 7.
  - positive-dim cells (r10/akslice.py: j random rational hyperplane slices; zero-dim primes of a j-slice are generic points of j-dim components): ranks 8, 7 and 6 at the sample points (partial run, r10/akslice.jsonl). Lower bounds are certain. "= generic rank" is probabilistic (random slice), not proof.
  - Rank 8 with [A|b] of rank 9 (σ-system inconsistent, so the fibre is empty by linear algebra alone) occurs on primes of (2,4,9,11), (3,4,9,10), (0,2,10,11) and (0,3,9,11).
- **Kernel at the rational rank-drop points** (r10/kernel.py → r10/kernel.json): every such K seen has row-projection ranks (0,1,3), or (0,0,4) for the witness. The kernel vectors are supported on the rows K misses, e.g. at (7,8,9,10) ker = <[−1,0,0,½,½ | 1,0,0,0,−1 | 0]>, …. Mechanism: C(κ,κ',·) ≡ 0 for κ, κ' in the same row, so a row-concentrated K loses C-rows. Conjecture, not proved: rank A_K < 8 ⇔ K is row-degenerate in this sense.
- **Push-down, the per-prime proof object.** For each minimal prime P of I_K: if rank 8, σ is the unique Q[a]/P-point (Cramer) and the remaining equations B(w_i,w_j), C(κ,w_i,w_j), C(w,w,w) become a K-ideal; if rank < 8, the σ-kernel parameters (8 − r per i) stay as variables. Computed as std(P + all fibre equations) over ℚ.
  - **All 18 zero-dim 𝒦 cells, every minimal prime: fibre empty over ℚ (E).** 59 primes in total. This supersedes R9 (14 M_p + 4 timeouts).
  - Positive-dim cells, whole-cell fibre std over ℚ (r10/fibcell.py, partial): empty (E) for (8,9,10,11), (4,8,10,11), (5,8,9,11), (6,8,9,10), (5,8,9,10), (4,5,10,11), (4,6,9,11), (4,7,9,10), (5,6,8,11), (5,7,8,10), (6,7,8,9) — 11 cells at snapshot; timeouts (150 s): (4,8,9,11), (4,8,9,10), (2,8,9,11), (3,8,9,10); run still going (r10/fibcell.jsonl). Every sampled point fibre in akslice is also empty.
  - Not yet covered: the rest of the 69 non-empty positive-dim cells and the 15–19 kgate timeouts. **LS(3,5) = 5 is NOT closed.**
- Stop condition (1), as instructed: the rank is below 16 on whole components, so the rank and kernel are reported above. The push-down was still done per prime, which is the case split the instruction asks for.

### Item 2: certificates
- E18 lifts (r10/lift18.sh, RR=0, mdeg 3, ℚ): **16/18 lifted and sympy-verified → V.** Every generator is identified as a P2/P3 coefficient or a colex minor (≤ 3); supports are 3–50 generators. The two others, (0,1,2,6,7,10) and (0,2,3,4,5,6), run out of memory in Singular lift at 4 GB with mdeg 3 and with mdeg 2. They stay E.
- **Stop rule triggered.** The difficult cells (R9 ddmin supports 198/1621, 260/824, 405/4056) still need ~200+ generators, and nothing in R10 reduced that. ddmin/minors-first is abandoned as the main route.
- **Structural decomposition, stated precisely (3×5, d = 6)**, replacing the per-L-cell certificates:
  0. (Lean, L157, done) level L ⊂ H, dim L = 6 ⇒ K = L ∩ R° has dim exactly 4 (≥ 6 − 2, ≤ 4).
  1. (algebra) L = K ⊕ graph(σ), σ: V_r → R°/K. The equations split as I_K (K-level), A_K σ_i = −b_i, and the residual R(σ) (B(w_i,w_j), C(κ,w_i,w_j), C(w_i,w_j,w_k)).
  2. (cover) Schubert cells of Gr(4,12) up to S3 × S4 (orbit-min pivot sets). Cells with 1 ∈ I_K get a small certificate each (123 cells).
  3. (components) for each non-empty cell, the minimal primes P of I_K.
  4. (linear elimination) rank r_P of A_K mod P. r = 8: σ by adjugate, so the certificate is 1 ∈ P + R(σ_P). r = 8 and rk[A|b] = 9: the certificate is just the inconsistency (a 9-minor ∉ P). r < 8: kernel parameters, so the certificate is 1 ∈ P + R(σ_0 + ker) in 2(8 − r) extra variables.
  5. Each stage has its own certificate. Current evidence is E (Singular std over ℚ) for stages 3–4 on the 18 zero-dim cells and part of the positive-dim cells. No V-level stage certificates have been extracted yet.
  - 4×5 d7: the analogue needs K = L ∩ R° in Gr(4,16) (dim K = 4 by L157), which is much bigger. Not started.

### Status (status10.json)
- 3×5 d6 (26 cells): V 16, E 2, T 2, M_p 2, O 4. Was V 0 / E 18.
- 4×5 d7 (80 cells): V 8, E 37, T 1, M_p 7, O 27 (unchanged).

### Claims ledger, R10
- NEW (E): the fibre over every point of the 18 zero-dim 𝒦 cells is empty (all 59 minimal primes, std over ℚ).
- NEW (V): 16 of the E18 3×5 cells now have rational certificates verified by sympy.
- NEW (fact, exact): A_K has rank 4 at the row witness. Ranks 5, 6 and 7 occur on zero-dim components (exact). So "generic rank 16 on 𝒦" is FALSE as a global statement.
- NEW (E, partial): whole-cell fibre empty over ℚ for the 11 positive-dim 𝒦 cells listed above (of 69).
- OBSERVATION (not proof): rank drop ⇔ row-degenerate K (5 rational points only).
- SUPERSEDED: R9 "18 zero-dim 𝒦 fibres: 14 M_p + 4 timeout" → now 18 E.
- UNCHANGED: LS(3,5) = 5 open; L_gct_219 open; no counterexample found.

- R10 final snapshot (runs killed 25 Nov 08:2x Manila / 01:2x CET; box clock jumped so 150 s caps were not honoured): whole-cell fibre empty over ℚ (E) for 18 of 69 positive-dim cells: (8, 9, 10, 11), (4, 8, 10, 11), (5, 8, 9, 11), (6, 8, 9, 10), (5, 8, 9, 10), (4, 5, 10, 11), (4, 6, 9, 11), (4, 7, 9, 10), (5, 6, 8, 11), (5, 7, 8, 10), (6, 7, 8, 9), (4, 5, 9, 11), (4, 6, 8, 11), (4, 6, 9, 10), (4, 7, 8, 10), (5, 6, 8, 10), (5, 7, 8, 9), (4, 5, 9, 10). Timed out/killed: (4, 8, 9, 11), (4, 8, 9, 10), (2, 8, 9, 11), (3, 8, 9, 10), (0, 8, 10, 11), (1, 8, 9, 11), (2, 8, 9, 10), (0, 8, 9, 11), (1, 8, 9, 10), (4, 5, 8, 11). akslice: 31 cells sampled, no non-empty sample fibre.

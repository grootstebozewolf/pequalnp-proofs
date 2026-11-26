# L-gct-219, case vJ: reduction, certificate, Lean

This is a single slice of L-gct-219, not a proof of L-gct-219. It covers only case vJ.

## The statement

L-gct-219 says that no 7-dimensional complex subspace `L` of `4 × 5` matrices is a
*level space* for the rectangular permanent at the all-ones matrix `J`. Level means
`perm(J + t) = 120` for every `t ∈ L`, where
`perm M = ∑_{e : Fin 4 ↪ Fin 5} ∏_r M(r, e r)`.

Case vJ comes from the case tree of the merged L-gct-215 proof (`Outside/L_gct_215.lean`,
abbrev `vJ`, proved there by `aEn`), moved down from dimension 8 to dimension 7.
`u L i` is the dimension of the part of `L` supported on row `i` alone:
`L ⊓ ⋂_{r ≠ i} ker(row r)`.

    vJ (L-gct-219):  ∀ L, level L → dim L = 7 → ∀ i, 4 ≤ u L i → False

In Lean this is `PEqualNP.Gct.Scratch219.VJ.vJ219`, stated with Mathlib notions only. It
does not mention msolve or the helper definitions.

## Decomposition: the smallest lemmas down to the finite object

1. **Row symmetry** (`vJ7`, from `aEn`). Permuting rows keeps the permanent, so `i = 0`.
2. **The row part is fixed** (from `aG7`). A matrix supported on row 0 is level iff its
   row sums to zero, a 4-dimensional space. So `u L 0 ≥ 4` means `L` contains it.
3. **Splitting off row 0** (from `aG7`). The permanent is linear in row 0. With the whole
   sum-zero row inside `L`, every `t ∈ L` has row 0 summing to zero. Rows 1–3 of every `t`
   satisfy `S1 = Q2 = G3 = 0` for every deleted column `j`. Then `dim L ≤ 4 + dim P`, where
   `P = L ∩ ker(row 0)`.
4. **Coordinates** (from `aG7`, `vN`). Rows 1–3 of a matrix in `P` have zero column sums.
   In cube-root-of-unity coordinates they become two vectors `a, b ∈ ℂ⁵`. The conditions
   become:
   - a quadric: `(2aᵢ − Σa)(2bᵢ − Σb) = Σa·Σb`;
   - five cubics: `g3_j(a) + g3_j(b) = 0`, where `g3_j` is 6·e₃ of the coordinates other than `j`.
5. **xO₂: `dim P ≤ 2`.** This is new; L-gct-215 needed only `≤ 3`. It splits as `xO` does:
   - If `Σa ≢ 0` and `Σb ≢ 0` on `P`, the quadric makes `(Σa, Σb)` injective, so
     `dim P ≤ 2`. This branch is copied unchanged from L-gct-215.
   - Otherwise assume `Σb ≡ 0` (swap `a` and `b` if not). The quadric factors, so for each
     `i` either `bᵢ ≡ 0` or `2aᵢ ≡ Σa`. That gives a support `S ⊆ {0..4}` and puts `P`
     inside a linear space `W_S`, of dimension 4 (`S ≠ ∅`) or 5 (`S = ∅`).
6. **The finite object.** For each of the 32 supports `S`, `W_S` contains no 3-dimensional
   subspace on which the five cubics vanish. That makes 32 statements; each is decided by
   one unit-ideal computation per chart.

So vJ follows from steps 1–5, which are dimension counting already checked in L-gct-215,
plus step 6. Step 6 is the only computational step.

## The certificate

- **Chart** (`VJChart.chart`). If `dim P ≥ 3`, three of the free coordinates of `W_S`,
  say `C`, map `P` onto `ℂ³`. Take `y_k ∈ P` with `τ_{k'}(y_k) = δ_{kk'}` for `k, k' ∈ C`.
  The remaining coordinates of the `y_k` are unknowns `m`: 3 of them when `S ≠ ∅`, 6 when
  `S = ∅`.
- **Evaluations.** Each `x = Σ s_k y_k ∈ P` with small integer `s` turns the cubic condition
  into a polynomial `E(m) = 0`.
- **Certificate.** Rationals or polynomials `g_i` with `Σ g_i E_i = 1`. There are
  `31·4 + 10 = 134` charts.

Every certificate turns out to use only 1–4 evaluations, and all of them are linear in `m`.

| file | role | trusted? |
|---|---|---|
| `ws.py`, `charts.py`, `empty.py` | the oracle: restricted cubics, and Gröbner bases of the chart ideals (sympy). All 134 come out ⟨1⟩, so we are on the QED branch, not QEX. | no |
| `gen.py` → `certs.json` | searches for cofactors over ℚ (python-flint row reduction) | no |
| `check.py` | independent re-check: recomputes each `E` from the definition of e₃, checks `Σ g E = 1` exactly, and checks that all 134 (support, chart) pairs are covered | no |
| `genlean.py` → `lean/PEqualNP/Gct/Scratch219/VJCore.lean` | emits one Lean lemma per support. Each chart ends in `linear_combination`, so the Lean kernel re-checks the identity. | no |
| `VJChart.lean`, `VJCore.lean`, `VJ.lean` | the Lean theorem | Lean kernel only |

msolve is not needed for this case. After the reduction the chart ideals have 3 or 6
unknowns and sympy decides them in under a second. The 4×5 msolve cells from the earlier
rounds (Schubert cells of Gr(7, 20), 33–57 unknowns) decide a different, finer split of
L-gct-219 that is still open. They do not enter here.

## Reproduce

    cd gct219-vJ
    python3 charts.py && python3 empty.py   # the oracle: unit ideal for every chart
    python3 gen.py                          # certs.json
    python3 check.py                        # independent check
    python3 genlean.py                      # VJCore.lean
    cd ../lean && lake build PEqualNP.Gct.Scratch219.VJ
    lake env lean --run <(echo '#print axioms PEqualNP.Gct.Scratch219.VJ.vJ219')

## Outcome: QED (for case vJ only)

`PEqualNP.Gct.Scratch219.VJ.vJ219` builds under the pinned Lean 4.36.0 and Mathlib.

    'PEqualNP.Gct.Scratch219.VJ.vJ219' depends on axioms: [propext, Classical.choice, Quot.sound]

The build has no `sorry`, no `native_decide` and no new axiom. The external computation is
not admitted: each of the 134 chart refutations is an explicit identity that the Lean
kernel re-checks with `linear_combination`. `VJCore` takes about 90 s on 4 cores.

The bound is sharp. `sharp.py` exhibits a 6-dimensional level space with a 4-dimensional
row-0 part: the sum-zero row 0, plus rows 1–3 supported on column 0 with zero column sum.
So vJ is exactly the step from 6 to 7.

This is not a submission. The files live in `Gct/Scratch219`, not `Outside/`. The other
cases of the L-gct-215 tree at dimension 7 are not started: MidCase, mI/eI, HighPair and vK.

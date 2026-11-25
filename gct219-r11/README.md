# Round 11 inputs: constant-pivot substitution

These scripts need the helper modules on `gct219-rounds` (`schubert.py`, `cell_solve.py`, `minorsw.py`).
`mkcell.py` puts `/home/user/gct219-rounds/gct219` on the import path. Edit that line for your checkout.

- `mkcell.py`: builds the Singular ideal of a 4 x 5 d7 cell. Generators are the P2..P4 coefficients plus the
  colex minors of degree <= 3, as in `minorsw.py`. A tail script is appended.
- `clp_tail.sing`: constant-pivot substitution. While some generator is `a*x_v + r` with `a` a nonzero
  constant and `x_v` not in `r`, it substitutes `x_v = -r/a`. It then writes the surviving variables and the
  reduced generators to OUTFILE. No denominators, no branching.
- `batch_clp.py`: substitution mod 32003 for every O and M_p cell in `r9/status9.json`, except
  `(1,2,5,7,10,11,15)` and the pilot `(2,3,5,6,7,10,11)`, plus an msolve test. The msolve column was run
  with Debian msolve 0.6.5, which crashes on these inputs. Treat `fail` as "not run".
- `batch_clp.jsonl`: per-cell results, giving unknowns before and after substitution and generator counts.
- `ctl_sub.py`: positive control. On a witness's canonical colex cell, every reduced generator must vanish at
  the witness. Result: 4x5 d6 row and column witnesses, cell (0,1,2,3,5,10), 0/278 nonzero.
- `stepq.py`: rung step 2. Substitution over Q, then `std` over Q, smallest reduced cell first.

To make an msolve input for one cell, run `python3 mkcell.py <S> 32003 3 out.sing clp_tail.sing`. Before that,
set OUTFILE in the tail. Then run `Singular -q out.sing`. The first line of OUTFILE holds the variables and the
other lines hold the generators: prepend `32003` as the second line to get the msolve format.

Pilot cell `(2,3,5,6,7,10,11)`: 61 -> 41 unknowns, 1621 -> 502 generators. `std` over Q gives the unit ideal
in 410 s and 1.1 GB. On the full system it times out at 600 s. `lift` on the reduced system runs out of
memory over Q (10.5 GB) and mod 32003 (6 GB cap).

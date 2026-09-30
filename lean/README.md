# The Watermark and Double Ladder Theorems in Lean 4

This folder holds complete Lean 4 proofs, with Mathlib, of two theorems about the lattice `V` of the `3m²` lines on the Fermat surface of prime degree `m ≥ 5`, with the form given by their intersection numbers:

- **The Watermark Theorem.** `V` is a free abelian group of rank `3(m−1)(m−2)+1`, and the Gram determinant of **every** `Z`-basis of `V` is exactly `m^{3(m−3)²}`.
- **The Double Ladder Theorem.** The discriminant group is `V*/V ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}` for every prime `m ≥ 7`, and `(Z/5)^{10} × Z/25` for `m = 5`.

For prime `m`, Shioda asked in 1987 whether `|det NS| = m^{3(m−3)²}` (Questions 7.2 and 7.4). Schütt, Shioda and van Luijk checked it by computer for odd `m ≤ 81`, and Aljovin, Movasati and Villaflor listed the elementary divisors by computer for `m ≤ 14`. Since the lines generate the Néron–Severi group for these `m` (Schütt–Shioda–van Luijk, Degtyarev), the two theorems give the discriminant of `NS` and its group. Each certificate, §10 and §9 respectively, records the literature, read in the original.

**Read first:**
- [watermark/LEAN_CERTIFICATE_WATERMARK_v2.pdf](watermark/LEAN_CERTIFICATE_WATERMARK_v2.pdf) ([Markdown](watermark/LEAN_CERTIFICATE_WATERMARK_v2.md));
- [double-ladder/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf](double-ladder/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf) ([Markdown](double-ladder/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.md)).

Each gives the theorem and its definitions exactly as Lean prints them, a line-by-line comparison with the paper, what is **not** formalized, the trust base, the procedure, the data of every piece, and how to reproduce everything.

## In one line

`Watermark.watermark_theorem` ([project/RequestProject/Watermark/W7.lean](project/RequestProject/Watermark/W7.lean)), `DoubleLadder.double_ladder_theorem` and `DoubleLadder.double_ladder_five` ([project/RequestProject/DoubleLadder/DL3.lean](project/RequestProject/DoubleLadder/DL3.lean)) compile with no `sorry`, no `native_decide` and no added axiom. They depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`.

## What is not formalized

Lean works with an explicit integer matrix `G` of size `3m² × 3m²`. That `G` is the matrix of intersection numbers of the lines on the complex Fermat surface is geometry: it is proved by hand in §1.4 of the Watermark certificate and checked by computer for `m = 5, 7, 11`, but it is not formalized. That the lines generate the Néron–Severi group is cited (Schütt–Shioda–van Luijk; Degtyarev).

## The papers

- *The Watermark Theorem* and *The Double Ladder Theorem* are in [../papers/](../papers/). They are also in the folder `hodge-fermat-campaign/` of [github.com/tretoef-estrella/chaise-longue-theorem](https://github.com/tretoef-estrella/chaise-longue-theorem), each next to its Lean certificate, with the instruments of June 2026 behind them.
- The Double Ladder Theorem is proved in Lean by the short integral argument of [double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.md](double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.md), not by the character route of the paper.
  - **Order:** `|V*/V| = m^{3(m−3)²}`, from the Watermark.
  - **Exponent:** `m² · V* ⊆ V`, from an explicit identity `G·Y·G = 6m²·G`.
  - **Rank:** `G mod m` has rank `12(m−3)`, or `26` for `m = 5`.

## Where the evidence is

| What you want to see | File |
|---|---|
| The Watermark theorem and its definitions as Lean prints them, the axioms, and a non-vacuity example at `m = 5` | [watermark/checkfinal.log](watermark/checkfinal.log) and, after the clean rebuild, [watermark/checkfinal_fresh.log](watermark/checkfinal_fresh.log); produced by [watermark/checks/CheckFinal.lean](watermark/checks/CheckFinal.lean) |
| The Double Ladder theorems, their definitions, the axioms, and non-vacuity examples at `m = 7, 11, 13` | [double-ladder/checkdlfinal.log](double-ladder/checkdlfinal.log), by [double-ladder/checks_lean/CheckDLFinal.lean](double-ladder/checks_lean/CheckDLFinal.lean) |
| The dependency cones of the final theorems | [watermark/deps_watermark.log](watermark/deps_watermark.log), [double-ladder/deps_dl.log](double-ladder/deps_dl.log) |
| Clean rebuilds from scratch | [watermark/clean_rebuild_2026-09-30.log](watermark/clean_rebuild_2026-09-30.log) (9 of 9 modules, one at a time) and [double-ladder/build_clean_all.log](double-ladder/build_clean_all.log) (Watermark and Double Ladder, 11 modules, exit 0, 333 s) |
| The local build and the printed statements of every run | `watermark/build_run1–7.log`, `watermark/check_run1–7.log`; `double-ladder/build_run*.log`, `double-ladder/check_run*.log` |
| The pieces exactly as sent to Aristotle | [watermark/pieces/](watermark/pieces/) (7), [double-ladder/pieces/](double-ladder/pieces/) (3) |
| The brute-force checks run before sending, with their negative controls | [watermark/checks/](watermark/checks/), [double-ladder/checks/](double-ladder/checks/) |
| The `m = 5` certificates of the Double Ladder split into lemmas, with identical statements | [double-ladder/DL2_split_m5.diff](double-ladder/DL2_split_m5.diff) |
| The state of every run, as kept during the work | [watermark/ESTADO_WATERMARK.md](watermark/ESTADO_WATERMARK.md), [double-ladder/ESTADO_DOUBLE_LADDER.md](double-ladder/ESTADO_DOUBLE_LADDER.md). These are working files, partly in Spanish, kept verbatim. |

## Paths in the certificates

The certificates name files as they were on the author's machine. In this folder:
- the Lean project `ARISTOTLE_LEAN/WATERMARK/proyecto/` is [project/](project/);
- everything else under `ARISTOTLE_LEAN/WATERMARK/` is in [watermark/](watermark/), with the same relative paths;
- everything else under `ARISTOTLE_LEAN/DOUBLE_LADDER/` is in [double-ladder/](double-ladder/), with the same relative paths.

Not published:
- the extracted projects returned by Aristotle (`run1/…`), because each is a full copy of the project at that stage;
- two Macaulay2 outputs of 1.6 MB and 118 MB (`kerG5.txt`, `kerG7.txt`), which [watermark/checks/kerexp5.m2](watermark/checks/kerexp5.m2) and [kerexp7.m2](watermark/checks/kerexp7.m2) regenerate;
- one empty log of an interrupted build.

## Contents

```
project/        the Lean project: lakefile.toml, lean-toolchain, lake-manifest.json and
                RequestProject/ (12 files, 5,233 lines): Main.lean, Watermark/Defs.lean,
                Watermark/W1–W7.lean, DoubleLadder/DL1–DL3.lean
watermark/      certificate, pieces, checks, logs and state file of the Watermark Theorem
double-ladder/  certificate, pencil proof, pieces, checks, logs and state file of the Double Ladder
```

Fingerprints of the 12 source files:
- SHA-256 of the concatenation, in sorted path order: `02ca3b3d8b06e9cc1a2dbd4827365bed630f30cbe1747eb7f8e064bde427f1aa`;
- SHA-256 of the list of their individual SHA-256 lines: `bb612c10e71963482901dff9ce489755a6cf855df4cceba241ec564951fcd8b0`.

The per-file values are in the Double Ladder certificate, §8.

## How to check it

You need `elan`, the Lean toolchain manager, and about 7 GB of disk for Mathlib. The build needs about 4.2 GB of memory at its peak, in `DL2.lean`. Toolchain `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

```
cd project
lake exe cache get
lake build
lake env lean ../watermark/checks/CheckFinal.lean
lake env lean ../double-ladder/checks_lean/CheckDLFinal.lean
```

The last two commands print the theorems, their definitions, their axioms and the non-vacuity examples.

## Who did what

- **Aristotle** (Harmonic) wrote the Lean proofs, one piece at a time. **The author and his team** wrote each piece from the papers.
- Every returned file was compiled again on the author's machine and audited against the paper before the next piece was sent. Nothing was accepted on Aristotle's word: the Lean kernel checks every proof.
- The proof that Lean follows for the Double Ladder was written by Claude (Anthropic) for the author, and is in `double-ladder/`.

**Author:** Rafael Amichis Luengo, Madrid.

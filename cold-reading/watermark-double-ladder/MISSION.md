# Cold reading — mission WM_DL_HEXAGON_1

Your name for this mission is **Grepy la Filigrana** (*filigrana* is Spanish for «watermark»). You are an independent referee. You have no stake in this work and owe it nothing. A watermark is checked against the light: your job is to hold every step up and say whether it is really there.

> ## NO AGENTS. NO SUBAGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE SESSION, EVEN IF «ULTRACODE» OR ANY SIMILAR MODE IS ON.

## 0. What you are reading
- **Under review:** `material/paper/watermark_double_ladder.tex` and its pdf, *The Watermark and Double Ladder Theorems* (12 pages). It is the text the author wants to deposit on the Hexagon preprint server. It proves, for the complex Fermat surface `S_m` of prime degree `m ≥ 5`:
  - Theorem 1 (Watermark): `|disc NS(S_m)| = m^{3(m−3)²}`;
  - Theorem 2 (Double Ladder): `NS(S_m)*/NS(S_m) ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}` for `m ≥ 7`, and `(Z/5)^{10} × Z/25` for `m = 5`.
  - The proof works with an explicit integer matrix `G` (§2), identified with the intersection matrix of the lines in §3.
- **The text is new as a paper.** It was written on 14 October 2026 from the earlier versions in `material/earlier_versions/` (Watermark v8, Double Ladder v4, the pencil proof v2) and the two Lean certificates in `material/lean_certificates/`. Its proof of Theorem 1 is *not* the proof of Watermark v8: it is the integral route of the Lean certificate (§3.1 there), written out by hand. Some steps were rewritten more simply than in the Lean pieces (for example `SAT ⊆ K` from Lemma 9, Lemma R.2 (Lemma 15) from Lemma 9, and the ranks of `SAT` and `K` without an injectivity lemma). **Nobody has read this text before you.**
- `material/sources/`: originals of the main citations — Schütt–Shioda–van Luijk (pdf and LaTeX source), Degtyarev (LaTeX source), Shioda 1987 (pdf and extracted text), Shioda 2015 (pdf and text), Aljovin–Movasati–Villaflor (pdf). Not provided: Shioda 1982, Aoki–Shioda 1983, Nikulin 1980, the Lean and Mathlib references; find what you can.
- `material/lean_certificates/`: what is checked in Lean. You cannot compile Lean here and you need not: use the certificates only to check what §10 of the paper says about them.

## JOB 1 — the mathematics, line by line (re-derive each proof by hand; say CORRECT, GAP or ERROR, and why)
- **M1. §2.** The definition of `G`; that it is symmetric; the table of incidence sets (re-derive each of the six rows from the definition); Lemma 4 (`GN_j = m𝟙`, `G𝟙 = 3m𝟙`).
- **M2. §3 (geometry).** Re-derive Proposition 5 (intersection numbers) from the equations of the lines, including the `+1` of families 0 and 2; Corollary 6 (the lattice of the lines is `A/ker G`; is the use of non-degeneracy correct? is primitivity needed anywhere?). Check the citations for «the lines span `NS ⊗ Q` iff `m ≤ 4` or `gcd(m,6) = 1`» and «the lines generate `NS` for `gcd(m,6) = 1`» against `material/sources/`.
- **M3. §4.** Lemma 7, Lemma 8 (R.1), and **Lemma 9 (G on pullbacks) in full**: every one of the six overlap formulas, including the shifts `u⁺`, `u⁻`. This lemma carries everything after it.
- **M4. §5.** The map `s_R` and its pullback form; Lemma 11 (`SAT ⊆ K`); **Lemma 12 (Lemma C, the count 12)**: the operator `δ`, the second-difference identities (signs and shifts), the step «both sides are one constant», the passage to quadratics, the sum-zero claim, injectivity of the parametrization; Remark 13; Lemma 14 (lifting).
- **M5. §6.** Lemma 15 (R.2): the expression `my = pb(mδ_c − 1) + N_0`, the three formulas for `Gy`, the congruences. Lemma 16 (census). **Proposition 17 (`mK ⊆ SAT`)**: the datum, the scalars `ε_1 = μ_0`, `ε_2 = −μ_2`, the shift in `w_2`.
- **M6. §7.** Lemma 18 (Gram of `F`: is the argument about overlap partner terms complete?); Corollary 19; Lemma 20 (index of `L_fam`); Lemma 21 (`F + SAT = L`); **Proposition 22** (ranks without an injectivity lemma; `[K:SAT] = m^{12}`: is `K ∩ mA = mK` used correctly?); Corollary 23.
- **M7. §8.** The determinant and the exponent arithmetic; the sign.
- **M8. §9 (Double Ladder).** Lemma 24 (`GYG = 6m²G`: the spanning set over `Q`, the action of `Y`, each eigen-piece); the minimal-polynomial remark; Corollary 25 (exponent); Lemma 26 (`G = SᵀΓS − mI` — check the shift convention of `Γ` against the families 0/2 incidence); Lemma 27 (relations: is the independence of the four `π^s` for `3 ≤ s ≤ m−1` correctly argued? is the polynomial-vs-function step correct?); Proposition 28; the `m = 5` paragraph (what exactly is claimed, and is it supported?); the assembly (elementary divisors, the count `n_0 = rank(G mod m)`).
- **M9. Corollary 3 (transcendental lattice):** Betti number, primitivity, Nikulin.
- **M10. Scope.** Is anything stated more strongly than it is proved? Is every use of `m ≥ 5`, `m` prime, `m` odd, `gcd(m,6) = 1` in place?

## JOB 2 — compute, with your own code (controls that CAN fail)
Write your own engines from the text alone. Python 3 (`numpy`, `sympy` if present) or anything installed. **Every run inside `zsh vigia.sh checks/LOGNAME.log 'command'`** (the log is the first argument; it kills the run at 1.2 GB or 10 minutes). Write the memory and time estimate in your report **before** each run. Never more than one run at a time.
- **C1.** Build `G` from §2 for `m = 5, 7` (and `11` if it fits). Check symmetry, Lemma 4, Lemma 9 (all six overlap formulas on a basis of `Z_0`; control: wrong shift fails), Lemma 11 (`SAT ⊆ K`).
- **C2.** Lemma 12: the dimension of the kernel of `s_{F_m}` is 12 for `m = 5, 7, 11, 13`; control: `m = 3` gives 11.
- **C3.** `rank K = 9m − 7`, `[K : SAT] = m^{12}`, `[Z^P : L_fam] = m^{(m²+m+2)/2}`, `[A : F + K]`, the Gram determinant of `F`, and the final `|disc V| = m^{3(m−3)²}` at `m = 5, 7` — at least one of these by a route independent of the paper (for example the Smith form of `G`).
- **C4.** `GYG = 6m²G` exactly (control: `6m G` fails); `G = SᵀΓS − mI` (control: shift in the other direction fails); `rank(G mod m) = 12(m−3)` for `m = 7, 11`, and `26` at `m = 5`; the Smith profile at `m = 5, 7` (and 11 if it fits) against Theorem 2 and the rows of [AMV, Table 1].
- **C5.** §3 numerically: build the three families of lines in `P³(C)` and decide, for every pair, whether they meet; compare with `G` at `m = 5, 7`. Control: `k + l − 1` instead of `k + l + 1`.

## JOB 3 — citations and literature
- **L1.** Check every entry of the bibliography (authors, title, journal, volume, year, pages, arXiv number) against an original or a reliable index (journal page, Crossref, arXiv). **The bibliography must be a LaTeX `thebibliography` with `\bibitem` entries and must not be empty**: say how many entries it has and whether every `\cite` resolves.
- **L2.** Check the history claims of §1 and §11 against the originals in `material/sources/`: Shioda 1987 (which questions, which pages, what «Added in proof» says), SSvL (end of §4: which `m`, what exactly was computed), Shioda 2015 (Conjecture 23), AMV (Table 1 rows for `m = 5, 7, 11, 13`).
- **L3.** A literature sweep: has anyone proved `|disc NS(S_m)| = m^{3(m−3)²}` for all primes `m`, or determined the discriminant group, before 2026? Search arXiv, Google Scholar, zbMATH, MathSciNet if reachable, and the papers citing SSvL and AMV. Download only originals; list every download in `checks/DOWNLOADS.md` (URL, time from `date`, md5) and every search in `checks/SEARCHES.md` (engine, query, time, hits, what you opened). A search that finds nothing is a result.
- **L4.** §10 against the two Lean certificates: are the theorem names, statements, axioms, and the list of what is not formalized reported faithfully? Is anything claimed for Lean that the certificates do not say?

## JOB 4 — presentation
Read the pdf page by page. Report rendering defects, wrong cross-references, undefined symbols, notation used before it is defined, sentences that a referee would misread.

## How to write — THE DISK RULE (this session may end without warning)
1. **First act:** create `REPORT_WM_DL_1.md` in this folder, with its section headings and nothing else.
2. After **every** item (M1, M2, …, C1, …) append its result to the report **before** starting the next one, with the time from `date`. What is only in your head does not exist.
3. Each item starts with `### <item> — STATUS: [DONE | NOT DONE | PARTIAL]`.
4. Keep a last line `NEXT: <item>` in the report so that you can resume after a cut.
5. If a run fails or a number is impossible, stop and say so; a bug is not a result.
6. Times only from `date`. Never delete a file.

## Grading scale
- **FATAL**: a statement is false or a proof cannot be repaired.
- **GAP**: a step is missing but the statement is plausibly true.
- **ERROR**: a wrong statement or citation that can be corrected without changing the results.
- **PRESENTATION**: everything else.

The first line of the finished report is the verdict: **HOLDS**, **HOLDS WITH CORRECTIONS**, or **DOES NOT HOLD**, then the counts of FATAL / GAP / ERROR / PRESENTATION. For every ERROR and PRESENTATION item, give the exact replacement text where you can.

## Where you may write
Only in this folder (`~/Desktop/LECTORES_EN_FRIO/WM_DL_HEXAGON_1/`). **Do not open anything in `~/Desktop/ARBOLYAML/`.** Do not sign in anywhere, do not post anything, do not send email.

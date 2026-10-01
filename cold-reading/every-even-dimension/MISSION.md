# Cold reading — «The Watermark in Every Even Dimension», version 2

You are a cold reader. You have never seen this work. Your job is to **break it**.

## What you read
`THE_WATERMARK_IN_EVERY_EVEN_DIMENSION_v2.md` (and its `.pdf`) in this folder. It claims four theorems on the discriminant of the lattice of Hodge classes of a Fermat variety, with proofs, and tables of verification.

## Rules
- Work **only inside this folder** (`~/Desktop/LECTORES_EN_FRIO/WATERMARK_THM_1/`). Do not open or write anything in `~/Desktop/ARBOLYAML/`. Do not launch other agents.
- **Ley del Disco:** first create `REPORT.md` here, with its section titles, before thinking; append to it after every step. What is not on disk does not exist.
- Every computation runs inside the guard: `zsh engines/vigia.sh LOG 'command'` (1.2 GB, 10 minutes). Write a one-line estimate of time and memory before each run. If a run is killed, say so; do not raise the limits.
- Write your own code for the checks; do not trust the engines you are given (you may read them and run them to compare).
- Sources in `sources/`: [AMV] (pdf and extracted text; the text is lossy, the tables must be read in the pdf), Looijenga arXiv:1005.1733 (pdf and text), Degtyarev–Shimada arXiv:1405.4683v3 (text), `PAPER_OFICIAL_v10.md` = [CL], `THE_REGULAR_CENTRALIZER_NOTE_v1.md` = [CL, Note]. You may fetch arXiv:2005.05583 ([BRR]) and other papers from the web.

## What to attack, in this order
1. **§1.3.** Is the quoted statement of Looijenga (Proposition 2.1, Corollary 2.2) exactly what the source says? Is `H° ≅ Z[G]/I_𝔄` justified? Is (1) (`Hdg° = I_T e`, `T(X) = I_𝔅 e`) correct, including for composite `m`?
2. **Theorem 1.** Every line of the proof. Is `H°/(Hdg° ⊕ T) → H/(Hdg ⊕ T)` really bijective? Is the isomorphism `G`-equivariant? Does it hold for every `m ≥ 3` as claimed, also even `m`? Remark (ii).
3. **Lemma 3.2, Lemma 3.3, Theorem 2.** Recompute the constant `κ = 2k(p−2) − 1` from scratch. Check the discriminant of `Z[ζ]`, the norm of `θ`, the factor `p^{−r}`, the treatment of complex conjugation, the generalized index, `|disc H°| = p`, `|disc Hdg°| = p^{E+1}`. Is «the index of `A_Y` in `Õ_Y` is a power of `p`» right?
4. **Theorem 3.** (a) the inequality and its direction. Lemmas 4.3, 4.4, 4.5 line by line: the filtration `Fil`, the congruences modulo `Fil^{j+1}`, the use of Wilson's theorem, the lifting argument, the freeness over `F_p[x_0^{p−1}]`, the passage from one form of the formula to the other (top degree, `sl_2` argument, comparison of Hilbert functions over `Q` and `F_p`). Is condition (C) exactly what [CL, Note, Proposition 3.1] gives, and are the hypotheses of [BRR, Proposition 2.12] satisfied for `Sp_{p−1}` in characteristic `p`? Read the Note and, if you can, [BRR].
5. **Theorem 4, Corollary 5, the surface paragraph.** In particular [DS, Corollary 1.6] (is `Λ_J` primitive, and are its characters `𝔅_J`?), the complete-intersection claim, the value of `δ_Y`, the cubic computation, `h_{[𝔅]}(j) = 3j`.
6. **The numbers.** With your own code, recompute in at least three cells: the delta invariants `δ_𝔄, δ_𝔅, δ_T` (definition in §3.1), the four identities of Theorem 2, the group of Table 4, the closed form of Theorem 4, and the formula of Theorem 3 from the Hilbert function of the ring in (C). Check Table 1 against the tables of [AMV] read in the pdf. Try to find a cell where anything fails. Try `p = 3` and small `k` by hand.
7. **Attributions and claims.** Is any statement stronger than its proof or its evidence? Is anything presented as new that you can find in the literature (search the web: discriminant of the Hodge lattice / transcendental lattice of Fermat varieties, congruence modules, Looijenga, Degtyarev, Shioda, Schütt–Shioda–van Luijk)? Is the status section (§10) accurate?

## What to deliver
`REPORT.md` in this folder, in English:
- a one-paragraph verdict: **HOLDS / HOLDS WITH CORRECTIONS / DOES NOT HOLD**;
- a numbered list of findings, each classified **FATAL / GAP / ERROR / PRESENTATION**, with the line of the note, what is wrong, and the correction you propose;
- what you verified and how (your scripts stay in this folder, with their logs);
- what you could not verify.
Be severe. A false theorem released is the worst outcome; a finding that kills a claim is a success.

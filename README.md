# The Watermark and Double Ladder Theorems

### The discriminant of the Néron–Severi lattice of a Fermat surface of prime degree, and its group — proved, and verified in Lean 4

**Rafael Amichis Luengo** · Madrid · tretoef@gmail.com

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23062529.svg)](https://doi.org/10.5281/zenodo.23062529)

> **Status.**
> - **Proved.** The Watermark Theorem was proved in June 2026. The Double Ladder Theorem was proved for every prime on 30 September 2026, by the short integral argument that the Lean proof follows.
> - **Verified in Lean.** Both are certified in Lean 4 with Mathlib (30 September 2026): no `sorry`, and only the three standard axioms. An independent cold reading of the Double Ladder certificate found no fatal error and no gap.
> - **What is not formalized** is stated below.
> - **Not refereed.** The results have not yet been refereed by a human expert.

---

## The theorems

Let `S_m ⊂ P³` be the complex Fermat surface `x₀^m + x₁^m + x₂^m + x₃^m = 0`. It contains exactly `3m²` lines. Let `V` be the lattice they span in `H²(S_m, Z)`, with the form given by their intersection numbers, and let `V*/V` be its discriminant group.

> **The Watermark Theorem.** For every prime `m ≥ 5`, `V` is a free abelian group of rank `3(m−1)(m−2) + 1`, and
>
> `disc V = m^{3(m−3)²}`.
>
> The Gram determinant of every basis of `V` has exactly this value, with sign `+`.

> **The Double Ladder Theorem.** For every prime `m ≥ 7`,
>
> `V*/V ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}`,
>
> and for `m = 5`, `V*/V ≅ (Z/5)^{10} × Z/25`.

For `m` prime to 6, the lines generate the Néron–Severi group: Schütt, Shioda and van Luijk proved it for `m ≤ 100`, and Degtyarev for every such `m`. So for every prime `m ≥ 5` the two theorems give the discriminant of `NS(S_m)` and its discriminant group. The Watermark gives the order of the group; the Double Ladder gives its structure.

| `m` | `disc V` | `V*/V` |
|---|---|---|
| 5 | `5^{12}` | `(Z/5)^{10} × Z/25` |
| 7 | `7^{48}` | `(Z/7)^{38} × (Z/49)^{5}` |
| 11 | `11^{192}` | `(Z/11)^{158} × (Z/121)^{17}` |
| 13 | `13^{300}` | `(Z/13)^{254} × (Z/169)^{23}` |
| 17 | `17^{588}` | `(Z/17)^{518} × (Z/289)^{35}` |
| 19 | `19^{768}` | `(Z/19)^{686} × (Z/361)^{41}` |

## In every even dimension (1 October 2026)

**[The Watermark in Every Even Dimension](papers/THE_WATERMARK_IN_EVERY_EVEN_DIMENSION.pdf)** ([markdown](papers/THE_WATERMARK_IN_EVERY_EVEN_DIMENSION.md)) · [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23091045.svg)](https://doi.org/10.5281/zenodo.23091045)

A sequel. Let `X` be the Fermat variety of degree `m` and dimension `2k`, `G = μ_m^{2k+2}/μ_m`, and `Hdg(X)` the lattice of integral Hodge classes of middle degree.

> **Theorem 1 (every degree `m ≥ 3`).** `Hdg(X)^∨/Hdg(X) ≅ Z[G]/(I_𝔅 + I_T)`: the discriminant group is the additive group of a finite ring, where `I_𝔅` and `I_T` are the ideals of the elements of `Z[G]` that vanish at the Hodge characters and at the other primitive characters.

> **Theorem 2 (prime degree `p`).** `|disc Hdg(X)| = p^E` with `E = 1 + (2k(p−2) − 1)·B − 2δ`, where `B` is the number of Hodge characters up to scalars and `δ` is the delta invariant of the order `Z_p[G]/I_𝔅`.

> **Theorem 3.** `δ` is the delta invariant of the tangent cone, the cone over the Hodge points of `P^{2k}(F_p)`. So `E = 1 + (2k(p−2) − 1)·B − 2·Σ_i ⌊i/(p−1)⌋·a(i)`, with `a` the Hilbert function of `F_p[x_0, …, x_{2k+1}]/(e_1, e_3, …, e_{2k+1}; x_i^{p−1})`.

> **Theorem 4.** The lattice spanned by the `p^{k+1}` linear spaces of one matching has discriminant `p^{1 + (p−1)^k·(k(p−2) − 1)}`.

For the Fermat cubic of dimension `2k` this gives `|disc Hdg(X)| = 3^{2·4^k + 1 − 3·C(2k+1, k)}`, and for surfaces it returns `3(p−3)²`, the Watermark.

| variety | `disc Hdg(X)` | |
|---|---|---|
| Fermat fourfold of degree 5 | `± 5^{303}` | as in Aljovin–Movasati–Villaflor |
| Fermat fourfold of degree 7 | `± 7^{2043}` | new; also computed from the linear cycles |
| Fermat fourfold of degree 11 | `± 11^{15603}` | new |
| Fermat sixfold of degree 5 | `± 5^{5596}` | new |
| Fermat cubic of dimension 8 | `± 3^{135}`, group `(Z/3)^{34} × (Z/9)^{34} × (Z/27)^{11}` | the exponent agrees with Aljovin–Movasati–Villaflor (who give the primitive lattice); the group is new |

**Status.**
- **Proved by hand**, not formalized in Lean. The proofs rest on Pham's theorem in the form given by Looijenga (arXiv:1005.1733, Corollary 2.2). Theorem 3 uses, in general, one dimension count that follows from a theorem of Bezrukavnikov, Riche and Rider (arXiv:2005.05583); without it the formula is a lower bound, and the count was checked by machine in 22 cells.
- **Read cold** by an independent reader before release: «holds with corrections», no fatal error; the corrections are in the text. The report, with the reader's own scripts and logs, is in [cold-reading/every-even-dimension](cold-reading/every-even-dimension).
- **Checked by seven engines**, against every row of prime degree of the tables of Aljovin, Movasati and Villaflor, at five composite degrees, and at the Fermat sextic surface against Auel, Böhning and Graf von Bothmer: [engines/every-even-dimension](engines/every-even-dimension).
- **Two conjectures are open:** that the exponent is a polynomial in `p` of degree `k + 1` (given in the note for `k ≤ 7`), and that the transcendental side is also governed by its tangent cone.
- **Not refereed.**

---

## What was known before

- **Shioda (1987)** asked, for prime `m`, whether `|det NS| = m^{3(m−3)²}` (Questions 7.2 and 7.4). He asked for the determinant only.
- **Schütt, Shioda and van Luijk (2010)** checked the value by computer for every odd `m ≤ 81`.
- **Aljovin, Movasati and Villaflor (2019)** listed the elementary divisors by computer for `m ≤ 14`. For `m = 5, 7, 11, 13` their rows are those of the table above.
- In **2015** Shioda still used the formula inside a conjecture.

As far as we could determine, no proof for all primes existed, and no general formula for the group had been stated. The sources, read in the original, are in §10 of the Watermark certificate and §9 of the Double Ladder certificate.

## How they are proved

**The Watermark.** The paper of June 2026 ([papers/THE_WATERMARK_THEOREM.pdf](papers/THE_WATERMARK_THEOREM.pdf)) proves it by explicit lattice computations with characters. The Lean proof follows a second route, entirely over the integers and without characters. The whole argument, in both routes, works with the explicit `3m² × 3m²` integer matrix of the lines.

**The Double Ladder.** Three facts fix the group:
1. the **order**, `|V*/V| = m^{3(m−3)²}`, which is the Watermark;
2. the **exponent**, `m² · V* ⊆ V`, from an explicit integer identity `G · Y · G = 6m² · G`;
3. the **rank of `G` modulo `m`**, which is `12(m−3)` for `m ≥ 7` and `26` for `m = 5`.

The group is then forced by counting. The proof is [lean/double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.pdf](lean/double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.pdf) ([Markdown](lean/double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.md)). The paper ([papers/THE_DOUBLE_LADDER_THEOREM.pdf](papers/THE_DOUBLE_LADDER_THEOREM.pdf)) gives the statement, the history of the law and an earlier route by characters.

## Verified in Lean 4

The final theorems are:
- `Watermark.watermark_theorem`, in [lean/project/RequestProject/Watermark/W7.lean](lean/project/RequestProject/Watermark/W7.lean);
- `DoubleLadder.double_ladder_theorem` and `DoubleLadder.double_ladder_five`, in [lean/project/RequestProject/DoubleLadder/DL3.lean](lean/project/RequestProject/DoubleLadder/DL3.lean).

They compile with Lean 4.28 and Mathlib, with no `sorry` and no `native_decide`, and they depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The project has 12 files and 5,233 lines.

**Read first, the two certificates:**
- [lean/watermark/LEAN_CERTIFICATE_WATERMARK_v2.pdf](lean/watermark/LEAN_CERTIFICATE_WATERMARK_v2.pdf);
- [lean/double-ladder/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf](lean/double-ladder/LEAN_CERTIFICATE_DOUBLE_LADDER_v2.pdf).

Each certificate states the theorem and its definitions exactly as Lean prints them. It compares them with the paper line by line and says what is not formalized. It gives the trust base, the data of every piece and every log, and how to reproduce everything.

**What is not formalized.**
- That the integer matrix used in Lean is the matrix of intersection numbers of the lines. This is geometry: it is proved by hand in §1.4 of the Watermark certificate and checked by computer for `m = 5, 7, 11`.
- That the lines generate the Néron–Severi group. This is cited (Schütt–Shioda–van Luijk; Degtyarev).

**How to check it.** You need `elan` and about 7 GB of disk; the build peaks at about 4.2 GB of memory.

```
cd lean/project
lake exe cache get
lake build
lake env lean ../watermark/checks/CheckFinal.lean
lake env lean ../double-ladder/checks_lean/CheckDLFinal.lean
```

The last two commands print the theorems, their definitions and axioms, and examples showing that the hypotheses are satisfiable (`m = 5`; `m = 7, 11, 13`). The details are in [lean/README.md](lean/README.md).

## How the Watermark was found

The formula was found on a single day, 4 June 2026, by reading published tables with two images in mind: a pressure test on a tanker of dangerous goods, and a result split into scattered pieces. The whole story, with what belongs to whom, is in [HOW_THE_WATERMARK_WAS_FOUND.md](HOW_THE_WATERMARK_WAS_FOUND.md) ([PDF](HOW_THE_WATERMARK_WAS_FOUND.pdf)).

The empirical law behind it, which includes an even-degree half that is still a conjecture, is *The Watermark Law*. It is in the Hodge–Fermat campaign, [chaise-longue-theorem/hodge-fermat-campaign](https://github.com/tretoef-estrella/chaise-longue-theorem/tree/main/hodge-fermat-campaign), together with the instruments and run logs of June 2026.

## Repository map

```
papers/                              the two papers: The Watermark Theorem, The Double Ladder Theorem (md and pdf)
                                     and the sequel, The Watermark in Every Even Dimension (md and pdf)
engines/every-even-dimension/        the seven engines of the sequel, with their logs
cold-reading/every-even-dimension/   the cold reading of the sequel: mission, report, the reader's scripts and logs
HOW_THE_WATERMARK_WAS_FOUND.md/.pdf  the story of the discovery
lean/                                the Lean 4 proofs
  README.md                          what is where, and how to reproduce it
  project/                           the Lean project (12 files)
  watermark/                         the Watermark certificate, pieces, checks, logs
  double-ladder/                     the Double Ladder certificate, its pencil proof, pieces, checks, logs
CITATION.cff · LICENSE · LICENSE-TEXT.md
```

## Who did what

- **The formula for prime degree, as a question:** Shioda (1987).
- **Its computer verification for odd `m ≤ 81`, and the proof that the lines span Néron–Severi:** Schütt, Shioda and van Luijk (2010), with Degtyarev (2015).
- **The method, and the tables for `m ≤ 14`:** Aljovin, Movasati and Villaflor (2019).
- **The unified law, the proofs and the Lean formalization:** the author, working with AI systems.
  - Claude (Anthropic) was his assistant and auditor.
  - Aristotle (Harmonic) wrote the Lean proofs from pieces written by the author's team.
  - Every Lean file was compiled again and audited on the author's machine before the next piece was sent.

## Related work

- *The Chaise Longue Theorem* (the same author): Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every degree in every even dimension (version 12, 4 October 2026; versions 7–10 covered the odd degrees), with its algebraic core verified in Lean 4. Zenodo [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150); repository [chaise-longue-theorem](https://github.com/tretoef-estrella/chaise-longue-theorem).

## References

- T. Shioda, *Some observations on Jacobi sums*, Adv. Stud. Pure Math. **12** (1987), 119–135.
- M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), 1939–1963.
- A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477.
- T. Shioda, *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, J. Math. Sci. Univ. Tokyo **22** (2015), 443–468.
- E. Aljovin, H. Movasati, R. Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184.
- E. Looijenga, *Fermat varieties and the periods of some hypersurfaces*, Adv. Stud. Pure Math. **58** (2010); arXiv:1005.1733.
- A. Auel, C. Böhning, H.-C. Graf von Bothmer, *The transcendental lattice of the sextic Fermat surface*, Math. Res. Lett. **20** (2013), 1017–1031.
- R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583.

## Licence and citation

The code is under the MIT licence ([LICENSE](LICENSE)). The texts are under CC BY 4.0 ([LICENSE-TEXT.md](LICENSE-TEXT.md)). How to cite: [CITATION.cff](CITATION.cff).

This repository, the two papers, the two certificates, the pencil proof and the story are archived on Zenodo: [doi.org/10.5281/zenodo.23062529](https://doi.org/10.5281/zenodo.23062529). The sequel has its own record: [doi.org/10.5281/zenodo.23091045](https://doi.org/10.5281/zenodo.23091045).

*Cite as:* Amichis Luengo, R. (2026). *The Watermark and Double Ladder Theorems (Verified in Lean)*. Zenodo. https://doi.org/10.5281/zenodo.23062529

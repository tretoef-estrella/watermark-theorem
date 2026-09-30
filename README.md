# The Watermark and Double Ladder Theorems

### The discriminant of the Néron–Severi lattice of a Fermat surface of prime degree, and its group — proved, and verified in Lean 4

**Rafael Amichis Luengo** · Madrid · tretoef@gmail.com

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

- *The Chaise Longue Theorem* (the same author): Conjecture 1.2 of Degtyarev–Shimada for the Fermat varieties of every odd degree in every even dimension. Zenodo [10.5281/zenodo.22961150](https://doi.org/10.5281/zenodo.22961150); repository [chaise-longue-theorem](https://github.com/tretoef-estrella/chaise-longue-theorem).

## References

- T. Shioda, *Some observations on Jacobi sums*, Adv. Stud. Pure Math. **12** (1987), 119–135.
- M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), 1939–1963.
- A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477.
- T. Shioda, *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, J. Math. Sci. Univ. Tokyo **22** (2015), 443–468.
- E. Aljovin, H. Movasati, R. Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184.

## Licence and citation

The code is under the MIT licence ([LICENSE](LICENSE)). The texts are under CC BY 4.0 ([LICENSE-TEXT.md](LICENSE-TEXT.md)). How to cite: [CITATION.cff](CITATION.cff).

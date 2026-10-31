# How the Watermark Was Found

### From a pressure test on a tanker to a theorem certified in Lean

**Rafael Amichis Luengo** · Madrid · 30 September 2026

*A note on the origin of the Watermark law and the Watermark Theorem: what was found, in what order, and what belongs to whom.*

> **Note of 30 October 2026.** A fuller and more precise account of how both theorems were found and proved is [HOW_THE_WATERMARK_AND_DOUBLE_LADDER_WERE_MADE.md](HOW_THE_WATERMARK_AND_DOUBLE_LADDER_WERE_MADE.md) ([PDF](HOW_THE_WATERMARK_AND_DOUBLE_LADDER_WERE_MADE.pdf)). It was written after going through every conversation and working document of the project. Where the two texts differ, that account is the reference. This note keeps the text of 30 September 2026, with its corrections of 14 October and its precisions of 30 October at the end; on 31 October §6 and the table of §8 were brought into line with that account.

---

## The result

For the Fermat surface of degree `m` in `P³`, let `V` be the lattice spanned by its `3m²` lines. The **Watermark Theorem** states that for every prime `m ≥ 5`,

> `|disc V| = m^{3(m−3)²}`.

When `m` is coprime to 6, the lines span the whole Néron–Severi lattice, by Schütt–Shioda–van Luijk together with Degtyarev. So the theorem computes the discriminant of the Néron–Severi lattice itself.

This note tells how the formula was found, in the order it happened. It all took place on a single day, 4 June 2026. The finding came out of a working exchange between the author and an AI assistant (Claude), with a second instance of the assistant auditing every step.

## 1. The cistern: weigh the whole, do not look inside

The work began inside a larger campaign on the Fermat varieties, around Conjecture 1.2 of Degtyarev–Shimada. The author put an intuition to the assistant in the form of an image:

> «a las cisternas de mercancías peligrosas se les somete a pruebas hidráulicas y neumáticas, y si hay la más mínima grieta, se sabe, aunque sea atómica. No hace falta meterse dentro con un estetoscopio.»

In English: tankers that carry dangerous goods are pressure-tested with water and air, and the smallest crack shows, however tiny; nobody has to climb inside with a stethoscope. The mathematical reading was just as short. If nothing is cracked, the whole object must weigh exactly `X`; so put it under pressure, measure the weight, and if the weight is not `X`, there is a crack.

The assistant's reply was that this hydraulic test already exists for surfaces. The discriminant is the weight: if the lines span the lattice, the determinant of their intersection matrix is forced to take a known value. The idea became a concrete instrument, a "pressure gauge": the Gram matrix of the linear cycles and its Smith normal form.

**What this image gave was the method: judge the whole object by one global number, instead of inspecting it piece by piece.** It did not give the formula.

## 2. The gauge, and the published tables it led to

The gauge was built and checked exactly against published values. The check also showed that its first "new" number was not new. Aljovin, Movasati and Villaflor (AMV) had already published it in Table 1 of their paper on the integral Hodge conjecture for Fermat varieties, and their Algorithm 1 is the same method. The claim of novelty was withdrawn at once.

Two things were left standing: an instrument that reproduced published numbers without being told them, and AMV's Tables 1–2, which list the elementary divisors of these lattices for degrees 3 to 14. The next step was to re-read those tables for a closed law, by hand and with no new machine runs.

## 3. Two laws

The re-reading produced two separate laws for the surfaces:
- **Law 1**, for prime degree `d`: the `d`-adic exponent of the discriminant is `3(d−3)²` (five of five rows: `d = 3, 5, 7, 11, 13`).
- **Law 2**, for degree `2q` with `q` an odd prime: the exponent at `2` is `12(q−1)(q−2)`, and the exponent at `q` is that number plus `6` (three of three rows). The constant gap of 6 had no explanation.

## 4. The scattered pieces: one law, not two

Then came the author's second image. In his words, a large result was hiding, not in one piece but split into loose parts so that nobody would catch it, and he could smell the trail of its parts. He asked the assistant to bring it in.

It was there. Law 1 and Law 2 were two faces of a single formula:

> **The Watermark law.** `|disc V| = m^{3(m−3)²}` for odd `m`, and `|disc V| = m^{3(m−3)²} · (m/4)³` for even `m`.

It fits all twelve rows of AMV's Table 1 (`m = 3, …, 14`) at once, prime powers included. The mysterious gap of 6 is the cube `(m/4)³ = (q/2)³`, split between the two primes: `−3` at the prime 2 and `+3` at `q`. Five further cells were predicted in writing before any computation: `m = 17, 19` (odd) and `m = 16, 18, 20` (even). All seven sealed exponents were met exactly. (For the odd ones, Schütt, Shioda and van Luijk had already computed the determinant, as was found afterwards.)

**What this second image gave was the unification: the conviction that two unrelated-looking laws were one.** The formula itself was read off the published tables.

## 5. What was already known

The literature was then checked against the law, with the sources read in full:
- **Shioda (1987)**, in *Some observations on Jacobi sums*, asked for the Fermat surface of **prime** degree `m` whether `|det NS| = m^{3(m−3)²}` (Questions 7.2 and 7.4, p. 133). For general `m` he gave divisibility only: the discriminant divides a power of `m`. The odd-prime formula is therefore Shioda's conjecture.
- **Schütt, Shioda and van Luijk (2010)**, in *Lines on Fermat surfaces*, computed by computer, for every odd `m ≤ 81`, the Gram determinant of their rational basis of lines and found `m^{3(m−3)²}` (end of their §4, "with exponent as conjectured" by Shioda); that basis spans the Néron–Severi lattice when `m` is coprime to 6 and `m ≤ 100`. They proved that the lines span the Néron–Severi lattice rationally, and in fact integrally when `m` is coprime to 6, with Degtyarev.
- **Shioda (2015)**, in *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, still used the formula as expected, not as proved: for `m` prime to 6 it appears inside his Conjecture 23 (§6.5).
- **Aljovin, Movasati and Villaflor (2019)** gave the method (Gram matrix and Smith normal form) and the tables in which the law was read. Their Table 1 lists, by machine, the elementary divisors of the lattice for every `m ≤ 14`. For the primes `m = 5, 7, 11, 13` their product is `m^{3(m−3)²}`, and the rows already show the group that the Double Ladder describes: `(Z/5)^{10} × Z/25` at `m = 5`, and `7^{38} · 49^{5}`, `11^{158} · 121^{17}`, `13^{254} · 169^{23}` at `m = 7, 11, 13`. They give no general formula and no proof.
- **The even half** of the law, with its factor `(m/4)³`, appears in none of these sources, nor in Degtyarev's survey. It remains a conjecture, tested blind in three even cells.

## 6. The names

The author chose both names, with the advice of the auditing assistant, each for its mechanism. For the first, he asked the auditor what the law really does; the auditor explained it and proposed four names, *Watermark* among them, and the author chose it. The mechanism behind the name: for prime degree `m`, only one prime appears in the discriminant, the degree itself, and its exponent `3(m−3)²` depends on the degree alone. The degree is stamped on the lattice like a watermark, which shows only when the whole sheet is held against the light, that is, when the lattice is judged whole, through one number.

The name *Double Ladder* was given on 5 June 2026. The author asked whether the second result was a theorem of its own and, if so, wanted a name with the words «double» and «ladder», both taken from the title of that morning's report by the building assistant; the auditor agreed that it was a theorem of its own (the Watermark says how much, the Double Ladder says what) and that the two words fit, and the author chose *The Double Ladder Theorem*. The group has factors of two sizes, `Z/m` and `Z/m²`, and the number of the larger ones is read from a ladder: at rung `ν` the rank drops by `6ν = 2 × 3ν`, and that factor 2 is why the ladder is double.

## 7. The proof, and Lean

The same night the odd prime half was proved, as the **Watermark Theorem**: for every prime `m ≥ 5`, `|disc V| = m^{3(m−3)²}`. The complete text passed a line-by-line audit; two of its steps (the inclusion `SAT ⊆ K` and the rank `9m − 7`) were checked by computer and not written for general `m`, and both are proved for every prime in the integral route below. Since the lines span the Néron–Severi lattice for such `m`, this answers Shioda's Question 7.4 (formula (7.10)) for the complex Fermat surface of every prime degree `m ≥ 5`, open since 1987. The June proof used the arithmetic of the cyclotomic field.

On 30 September 2026 the theorem was **certified in Lean 4**, along a second route that is entirely integral and uses no characters. The formal statement (`Watermark.watermark_theorem`) says that `V` is free of rank `3(m−1)(m−2)+1` and that, for every prime `m ≥ 5` and every basis of `V`, the Gram determinant equals `m^{3(m−3)²}`, with positive sign. The proof depends only on the three standard axioms of Lean's logic. The formal proofs were written by the AI system Aristotle (Harmonic), then compiled and audited independently on the author's machine; the Lean certificate lists every step. Lean does not check two things, and the paper says so: that the Gram matrix is the intersection matrix of the lines (proved by hand), and that the lines generate the Néron–Severi lattice (Schütt–Shioda–van Luijk and Degtyarev).

The sequel, the **Double Ladder**, gives the structure of the discriminant group and not only its order: `V*/V ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}` for every prime `m ≥ 7`, and `(Z/5)^{10} × Z/25` for `m = 5`. Its profile law was already among the June findings. It was proved by a short integral argument on 30 September 2026 and certified in Lean the same day, in the same project; it has its own Lean certificate.

## 8. Who did what

| What | Owner |
|---|---|
| The formula for prime degree, as a question (1987) | T. Shioda |
| The determinant checked by computer for every odd `m ≤ 81`; the lines span `NS ⊗ Q` | M. Schütt, T. Shioda, R. van Luijk (2010) |
| The lines generate `NS(S_m)` over `Z` for `gcd(m, 6) = 1` | A. Degtyarev (2015), with Schütt–Shioda–van Luijk |
| The method (Gram matrix of linear cycles and Smith form) and the tables, with the group for `m ≤ 14` | E. Aljovin, H. Movasati, R. Villaflor Loyola (2019) |
| Direction, choice of targets, the images and questions, the names (with Claude's advice) | R. Amichis Luengo |
| The unified law, the sealed predictions, the June proofs (4–5 June 2026) | a Claude instance (the builder), audited by another Claude instance |
| The integral proof of 30 September and the paper | Claude instances |
| The Lean proofs | Aristotle (Harmonic), compiled and audited on the author's machine |
| Independent cold readings (pencil proof, Lean certificate, paper) | three separate Claude instances |

## References

1. T. Shioda, *Some observations on Jacobi sums*, Adv. Stud. Pure Math. **12** (1987), 119–135.
2. M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), 1939–1963. doi:10.1016/j.jnt.2010.01.008
3. A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477. doi:10.1016/j.jnt.2014.07.020
4. E. Aljovin, H. Movasati, R. Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184. arXiv:1711.02628
5. T. Shioda, *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, J. Math. Sci. Univ. Tokyo **22** (2015), 443–468.
6. A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties*, J. Math. Soc. Japan **68** (2016), 975–996. arXiv:1405.4683

---

*Corrections of 14 October 2026 (copy attached to the Hexagon deposit of «The Watermark and Double Ladder Theorems»).* Two sentences of the note of 30 September 2026 are corrected here: §5, Schütt–Shioda–van Luijk computed the determinant on their basis of lines, which is the Néron–Severi lattice only when `gcd(m, 6) = 1`; §7, the June proof had two steps checked by computer only. Nothing else is changed.

*Precisions of 30 October 2026.* The saved conversations of June 2026 were read again in full, and the following points are made precise here.
- §7, the Watermark Theorem. As the corrections of 14 October say, two steps of the June proof were checked by computer only; the proof for every prime is the integral route of 30 September 2026, certified in Lean.
- §7, the Double Ladder. Its statement and a first argument, through a rank that drops like a ladder, date from 5 June 2026; four steps of that argument were checked by computer at a few primes only. The proof for every prime is the one of 30 September 2026.

*Revision of 31 October 2026.* §6 now tells how both names were chosen, as the fuller account of 30 October does, and the table of §8 is the one of that account (the earlier table credited the author with reading the unified law in the tables; in the record it was read by the building assistant). Two sentences were added, in §4 and §7. Nothing else is changed.

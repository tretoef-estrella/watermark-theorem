# THE DOUBLE LADDER THEOREM — LEAN CERTIFICATE
## A machine-checked proof, in Lean 4 with Mathlib, of the structure of the discriminant group of the lattice of lines on the Fermat surface of prime degree

**Rafael Amichis Luengo** · Madrid, Spain · tretoef@gmail.com

Certificate v2 · 30 September 2026. v2 corrects v1 (the same day) after a cold read by an independent reader, who found no fatal error and no gap: four wrong statements and several unclear ones in the text of the certificate, listed in §11. The Lean content, the numbers and the fingerprints are unchanged.

Companion to *The Double Ladder Theorem* (R. Amichis Luengo, 5 June 2026, version 4 of 30 September 2026), file `hodge-fermat-campaign/THE_DOUBLE_LADDER_THEOREM.md` of `github.com/tretoef-estrella/chaise-longue-theorem` and `papers/THE_DOUBLE_LADDER_THEOREM.md` of `github.com/tretoef-estrella/watermark-theorem`; to the proof that the Lean formalization follows, [DL-Pencil]; and to the *Lean Certificate* of *The Watermark Theorem* [WM-Lean], on which it builds. The Lean project and all the evidence are in the repository `watermark-theorem`, folder `lean/`.

---

## 0. Verdict

Let `m` be a prime and `V` the lattice spanned by the `3m²` lines of the Fermat surface of degree `m`, with the bilinear form given by their intersection numbers. Its discriminant group is `D = V*/V`, where `V* = Hom(V, Z)` and `V` sits in `V*` through the form. Lean 4 proves:

- for every prime `m ≥ 7`: **`D ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}`**;
- for `m = 5`: **`D ≅ (Z/5)^{10} × Z/25`**.

These are exactly the statements of the paper. The *order* of `D`, `m^{3(m−3)²}`, is the Watermark Theorem, certified in Lean in [WM-Lean]. This certificate adds its *structure*: the exponent divides `m²`, and the number of cyclic factors of order `m²` is `3m − 16` (`1` at `m = 5`).

The whole proof compiles on the author's Mac, including the case `m = 5`. It contains no `sorry`, no `admit`, no `native_decide` and no added axiom. Both final theorems depend only on the three standard axioms of Lean and Mathlib: `propext`, `Classical.choice` and `Quot.sound`.

**What Lean certifies, and what it does not.** As for the Watermark, Lean works with the explicit integer matrix `G` of size `3m² × 3m²` defined in `Watermark/Defs.lean`, and with `V = Z^{3m²}/ker G` carrying the form induced by `G`. That `G` is the intersection matrix of the lines on the complex Fermat surface is geometry: it is proved by hand and checked by computer in [WM-Lean, §1.4], and it is not formalized. That `V` is the whole Néron–Severi group for prime `m ≥ 5` is a cited theorem [SSvL, Deg]. So:

> **Lean certifies the lattice statement completely. The statement about the Néron–Severi group of the Fermat surface follows from it by the identification of [WM-Lean, §1.4], proved by hand and checked by computer, and by the cited results of [SSvL] and [Deg].**

**The paper's own proof is not the one formalized.** The June paper proves the theorem by characters, shadows and a «rank ladder». Four steps there, in its §4 and §6, were confirmed at three or four primes and not written for general `m` (its version note lists them). The Lean proof follows a different, shorter route, written for general `m` [DL-Pencil] (§3 below), which does not need those steps.

§1 states exactly what is proved. §2 states exactly what is not. §3–§8 describe how it was proved and how to check it. §9 records what was already known.

---

## 1. The certified statement

### 1.1 The theorems, verbatim

Printed by Lean with `#check` and `#print axioms` (log `check_run3_clean.log`, after a clean rebuild of the whole project):

```
double_ladder_theorem : ∀ (m : ℕ) [inst : Fact (Nat.Prime m)],
  7 ≤ m → Nonempty (D m ≃+ (Fin (3 * m ^ 2 + 59 - 24 * m) → ZMod m) × (Fin (3 * m - 16) → ZMod (m ^ 2)))

double_ladder_five : Nonempty (D 5 ≃+ (Fin 10 → ZMod 5) × ZMod 25)
```

```
'DoubleLadder.double_ladder_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'DoubleLadder.double_ladder_five' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`≃+` is an isomorphism of additive groups. `Fin n → ZMod k` is the group `(Z/k)^n`.

### 1.2 The definitions it uses, verbatim

The statement uses one new definition, in `RequestProject/DoubleLadder/DL3.lean`, printed by `#print` in `check_run3_clean.log`:

```
@[reducible] def DoubleLadder.D : (m : ℕ) → [NeZero m] → Type :=
fun m [NeZero m] => Module.Dual ℤ (V m) ⧸ LinearMap.range (formV m)
```

Everything else — `Line`, `gram`, `K`, `V`, `formV` — is the Watermark's, in `RequestProject/Watermark/Defs.lean`. It is printed verbatim in [WM-Lean, §1.2], and its faithfulness to the lines of the Fermat surface is audited there line by line [WM-Lean, §1.3]. The Watermark files used here are **byte-identical** to those certified in [WM-Lean]: their SHA-256 fingerprints, listed in §8, are the same as in [WM-Lean, §8].

`formV m` is a bilinear form on `V m`, that is, a linear map `V m → Module.Dual ℤ (V m)`. Its range is the image of `V` in `V*`. So `D m` is `V*/V`, the discriminant group of the lattice `V`.

### 1.3 Faithfulness to the paper, line by line

The paper is *The Double Ladder Theorem*, Abstract and §1. The statement is the same in versions 2 (5 June 2026, md5 `7b10b75d…`), 3 and 4 (30 September 2026); version 4 is the one published with this certificate.

| Paper | Lean | Agreement |
|---|---|---|
| `S_m`, prime `m ≥ 7` | `[Fact (Nat.Prime m)]`, `7 ≤ m` | Identical, and no other hypothesis. |
| `m = 5` | `double_ladder_five`, stated at `m = 5` | Identical. |
| `V = NS(S_m)`, the lattice of the lines | `V m` of the Watermark, with `formV m` | The lattice of the lines, as in [WM-Lean, §1.3–§1.4]. `V = NS` is cited, §2. |
| the discriminant group `V*/V` | `D m = Module.Dual ℤ (V m) ⧸ range (formV m)` | Identical (§1.2). |
| `≅` | `Nonempty (D m ≃+ …)` | An isomorphism of abelian groups exists. |
| `(Z/m)^{3m²−24m+59}` | `Fin (3 * m ^ 2 + 59 - 24 * m) → ZMod m` | Identical. Subtraction in `ℕ` does not truncate: `3m² + 59 − 24m` is written with the subtraction last, and `3m² − 24m + 59 > 0` for every `m` (its discriminant is `576 − 708 < 0`). |
| `(Z/m²)^{3m−16}` | `Fin (3 * m - 16) → ZMod (m ^ 2)` | Identical. No truncation: `3m − 16 ≥ 5` for `m ≥ 7`. |
| `(Z/5)^{10} × Z/25` | `(Fin 10 → ZMod 5) × ZMod 25` | Identical. |

**Consistency with the Watermark.** The order of the group in the statement is `m^{3m²−24m+59} · m^{2(3m−16)} = m^{3m²−18m+27} = m^{3(m−3)²}`, and `5^{10} · 25 = 5^{12}`: the order certified in [WM-Lean]. This is also how Lean proves it (§3.1, step 4).

**Non-vacuity.**

- The hypotheses can be satisfied, and the statement is a concrete isomorphism, not a statement about an empty object. The file `checks_lean/CheckDLFinal.lean` instantiates the theorem at `m = 7, 11, 13` and obtains, in Lean:
  - `D 7 ≃+ (Z/7)^{38} × (Z/49)^{5}`;
  - `D 11 ≃+ (Z/11)^{158} × (Z/121)^{17}`;
  - `D 13 ≃+ (Z/13)^{254} × (Z/169)^{23}`.

  The file compiles with no error: exit 0, 99 s, peak 2.20 GB (`checkdlfinal.log`, 30 Sep, after the clean rebuild). The same run prints the two final theorems with their axioms, `D`, `Y`, and four intermediate theorems (`gram_mul_ylad_mul_gram`, `exists_formV_eq_smul`, `rank_gram_map`, `rank_gram_map_five`), with the axioms of three of them (all but `exists_formV_eq_smul`). The axioms of every theorem in the cone are contained in those of the final theorems, which are `[propext, Classical.choice, Quot.sound]`.
- These three profiles, and the profile at `m = 5`, are the rows `(2,5)`, `(2,7)`, `(2,11)`, `(2,13)` of Table 1 of Aljovin–Movasati–Villaflor [AMV], who computed them by machine, one cell at a time (§9).

---

## 2. What is not certified

1. **The geometry.**
   - That `G` is the intersection matrix of the lines on `S_m`: proved by hand and checked by computer at `m = 5, 7, 11` in [WM-Lean, §1.4]; not formalized.
   - That `A/ker G` is the lattice of lines in `H²(S_m, Z)`: standard, cited in [WM-Lean, §1.4].

   Mathlib has no complex algebraic surfaces and no singular cohomology of them.
2. **The equality `V = NS(S_m)`** for prime `m ≥ 5`: [SSvL] for `m ≤ 100`, [Deg] for every `m` prime to `6`; cited. With it, the theorem gives the discriminant group of `NS(S_m)`.
3. **The corollaries of the paper's §8** are not formalized.
   - The transcendental lattice `T_m` has the same discriminant group, because `H²(S_m, Z)` is unimodular. This is standard lattice theory [Nik], applied to a geometric input; it is not formalized.
   - The Brauer group consequences are not formalized.
4. **The paper's own proof is not the proof formalized.** Lean follows the route of §3.1, which is that of [DL-Pencil]: the same three facts and the same assembly. Three details differ, listed in [DL-Pencil, §7]; the main one is that Lean does not take a Smith form but counts `|D|` and `|D/mD|` (step 4 of §3.1). It is a second, independent proof of the same statement.
5. **Faithfulness is an audit, not a theorem.** Lean guarantees that the proof is correct for the statement as written. That the statement says what the paper says is checked in §1.3. A reader should check §1.2–§1.3 here and in [WM-Lean]: the definition `D` above, the file `Defs.lean`, and six cases of `gramUpper`.
6. **Timing data.** Aristotle's own start and end times were not exported. The times in §6 are the download times of the result files.

---

## 3. How the proof is organised in Lean

The proof was cut into three pieces, DL1–DL3, sent to Aristotle in the Watermark's project (the Double Ladder uses the Watermark's definitions and theorems). Each piece is a self-contained Markdown file in `pieces/` with Setting, Statements, Proof and Checks, and produced one Lean file in `RequestProject/DoubleLadder/`. No piece modified a file of an earlier piece: the Watermark files W1–W7, `Defs`, `Main`, `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` were byte-identical in every returned project.

| # | Piece | Content | Lean file | Main Lean results |
|---|---|---|---|---|
| DL1 | `dl1_exponent.md` | the certificate matrix `Y`; `G Y G = 6m² G`; `m²·V* ⊆ V` | `DL1.lean` | `ylad`, `gram_mul_ylad_mul_gram`, `exists_toMatrix_mul_eq`, `exists_formV_eq_smul` |
| DL2 | `dl2_rank_mod_m.md` | the shadow factorization `G = SᵀΓS − mI`; the 6 relations per family; `rank(G mod m) = 12(m−3)` for `m ≥ 7`; `26` at `m = 5` | `DL2.lean` | `gram_eq_shadow`, `ker_relMap_eq_span`, `finrank_ker_relMap`, `sum_mul_shift_eq_zero`, `rank_gram_map`, `rank_gram_map_five` |
| DL3 | `dl3_assembly.md` | `D ≅ Z^ι/range M`; `|D| = |det|`; `m²D = 0`; `|D/mD| = m^{r − rank M̄}`; the group-structure lemma; the two final theorems | `DL3.lean` | `discrEquiv`, `card_coker`, `sq_smul_discr_eq_zero`, `card_coker_quot_smul`, `equiv_of_card`, `double_ladder_theorem`, `double_ladder_five` |

### 3.1 The chain of the final theorem

This is how `double_ladder_theorem` is proved in Lean. Every step is a Lean proof. Here `m ≥ 7` is prime, `G` is the Watermark's matrix, `r = rank V = 3(m−1)(m−2) + 1`.

1. **The order** (Watermark, W7). For any `Z`-basis of `V`, `det Gram = m^{3(m−3)²}`. In DL3 this becomes `|D| = m^{3(m−3)²}` (`card_coker`, via Mathlib's `Submodule.natAbs_det_equiv`).
2. **The exponent** (DL1). Let `Y` be block diagonal over the three families, with `Y = P_k + P_l + 3P_{k−l} + 3P_{k+l} − 6m·I` on each family, where `P_π(p, q) = 1` when the pencil `π` takes the same value at `p` and `q`. Then **`G Y G = 6m² G`** over `Z`. It is proved on the pullback vectors of W4 and the family vectors. `Y` acts on each of them by a scalar. So does `G`, except on the overlap pullbacks, which come in pairs `v, v′` with `Gv = −m v + m v′`; Lean treats each pair jointly (`defect_pair`). It follows that `6m²·V* ⊆ V`. Since `|D|` is a power of the prime `m ≥ 5`, `6` is invertible on `D`, so **`m²·D = 0`** (`exists_formV_eq_smul`, `sq_smul_discr_eq_zero`).
3. **The rank modulo `m`** (DL2).
   - Modulo `m`, `G` factors through twelve «shadows»: for each family and each pencil `π ∈ {k, l, k−l, k+l}`, the map that sums a function over the fibres of `π`. Over `Z`, **`G = SᵀΓS − m·I`**, with `Γ` an explicit symmetric matrix on the twelve shadow slots (`gram_eq_shadow`).
   - The annihilator of the image of `S` is spanned by six relations per family (three constants, two linear, and the polarization identity `(k+l)² + (k−l)² = 2k² + 2l²`), and no others (`ker_relMap_eq_span`, `finrank_ker_relMap`). Lean proves this with mixed second differences of functions on `Z/m` (`LemmaC.secondDiff`), not by writing functions as polynomials of degree `≤ m − 1` as the pencil proof does; the statement is the same.
   - The image of `Γ` on the relations lies back in the image of `S` when `m ≥ 7`, because every pairing involved is `Σ_{x ∈ F_m} p(x)q(x)` with `deg(pq) ≤ 4 ≤ m − 3`, and `Σ_x x^s = 0` for `s ≤ m − 2` (`sum_mul_shift_eq_zero`).
   - Together: **`rank_{F_m}(G mod m) = 12(m − 3)`** (`rank_gram_map`).
4. **The assembly** (DL3). `D/mD` has `m^{r − rank(G mod m)}` elements (`card_coker_quot_smul`). A finite abelian group `H` with `m²H = 0`, `|H| = m^N` and `|H/mH| = m^c` is `(Z/m)^{2c−N} × (Z/m²)^{N−c}` (`equiv_of_card`, a general lemma). Here `N = 3(m−3)²` and `c = r − 12(m−3) = 3m² − 21m + 43`, so `N − c = 3m − 16` and `2c − N = 3m² − 24m + 59`.

**The case `m = 5`** (`double_ladder_five`). Steps 1, 2 and 4 are the same. Step 3 changes, because `Σ_{x∈F_5} x⁴ = −1 ≠ 0`: the degree-4 pairings survive and the rank is `26`, not `12(5−3) = 24`. Lean proves `rank(G mod 5) = 26` by two explicit certificates over `ZMod 5`, checked by evaluation in the kernel (`decide +kernel`): a factorization `Ḡ = B·C` through `26` columns (so the rank is at most `26`), and a `75 × 26` matrix `Y₅` such that `26` chosen rows of `Ḡ` times `Y₅` give the identity `I₂₆` (so the rank is at least `26`). Then `c = 37 − 26 = 11`, `N = 12`, `N − c = 1`, `2c − N = 10`.

### 3.2 The dependency cone

The Lean program `checks_lean/DepsDL.lean` collects every declaration of the project that `double_ladder_theorem` and `double_ladder_five` use, directly or indirectly.

Result (`deps_dl.log`, exit 0, 106 s):

| Module | `double_ladder_theorem` | `double_ladder_five` |
|---|---|---|
| `Watermark.Defs` | 38 | 38 |
| `Watermark.W1` | 34 | 34 |
| `Watermark.W2` | 81 | 81 |
| `Watermark.W3` | 38 | 38 |
| `Watermark.W4` | 31 | 31 |
| `Watermark.W5` | 50 | 50 |
| `Watermark.W6` | 103 | 103 |
| `Watermark.W7` | 44 | 44 |
| `DoubleLadder.DL1` | 47 | 47 |
| `DoubleLadder.DL2` | 96 | 125 |
| `DoubleLadder.DL3` | 47 | 41 |
| **Total** | **609** | **632** |

Every file of the Watermark and of the Double Ladder is on the path of both final theorems; only the header `Main.lean` (no declarations) is not. Every one of these declarations is checked by the kernel as part of the final theorems. For `m = 5` the cone has 29 more declarations of `DL2` (its explicit certificates) and 6 fewer of `DL3` than for `m ≥ 7`. These are differences of counts; the two cones were not compared declaration by declaration.

---

## 4. Trust base

- **What must be trusted:**
  - the Lean 4 kernel, toolchain `leanprover/lean4:v4.28.0`;
  - Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`);
  - the three standard axioms `propext`, `Classical.choice`, `Quot.sound`;
  - the audit of the statement (§1.3 here and in [WM-Lean]) and the geometry of [WM-Lean, §1.4].
- **What need not be trusted:** Aristotle (Harmonic), the AI system that wrote the Lean proofs, and the author's brute-force checks. Every file was compiled again on the author's machine, and the kernel re-checks every proof.
- **Forbidden constructs, searched as whole words in the three Double Ladder files:** none of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `csimp`, `partial`, `macro`, `elab`, `syntax`, `notation`, `debug` occurs. (For the nine Watermark files, see [WM-Lean, §4]; they are unchanged.)
- **`decide`.** It occurs, and every occurrence is kernel evaluation, not native code:
  - `DL1.lean`, once: `interval_cases m <;> … <;> decide`, on small numbers;
  - `DL2.lean`: the `m = 5` certificates, `decide +kernel`, 41 small lemmas, plus `by decide` for indices `⟨0, by decide⟩ : Fin 3`.

  `decide +kernel` asks the kernel itself to evaluate a decidable proposition. It adds nothing to the trust base, unlike `native_decide`, which does not occur.
- **Options.** `DL2.lean` sets `maxRecDepth 100000` on 43 declarations (the `m = 5` certificates and their assembly). This raises an elaboration limit; it does not affect soundness. `DL1.lean` and `DL3.lean` set no option.
- **Axioms of every main theorem**, printed after each piece (`check_run1.log`, `check_run2_general.log`, `check_run3.log`, `check_run3_clean.log`): always `[propext, Classical.choice, Quot.sound]`.

---

## 5. The procedure

The procedure is that of [WM-Lean, §5] and of the Chaise Longue certificate [CL-Lean]: write a self-contained piece; check it by brute force before sending, with a negative control; send it to Aristotle (project `884019b5-ec06-4ff7-8a7b-8d8a1f18d0a1`); reload the project page and confirm the task finished before downloading; diff against the local project; grep for forbidden constructs; build locally inside a watchdog; print statements and axioms; audit faithfulness; record the run in `ESTADO_DOUBLE_LADDER.md`.

**Stop conditions, fixed in advance:** a property NEGATED by Aristotle; a statement that is not faithful; a build failure; a `sorry` or an extra axiom; a change to an old file. **None occurred.**

**The one local change to Aristotle's output, stated in full.**
- Aristotle's `DL2.lean` proved each of the two `m = 5` certificates as **one** `decide +kernel` theorem: `hBC` (75 rows) and `hXY` (26 rows). On Aristotle's machine this took about 2 minutes.
- On the author's Mac (8 GB) the local build did not finish. The kernel's cache grows within a single declaration: one row costs about 2 s and no memory; 25 rows in one theorem cost about 49 s and 1 GB more (logs `test5_*.log`). We estimate, from these measurements, that the whole certificate in one theorem needed about 9 GB, so the machine swapped; no log records that figure. The first watchdog measured only resident memory and did not see it; the watchdog now measures the real footprint.
- **Fix:** `hBC` was split into 15 lemmas, one per `(family, a)`, and `hXY` into 26 lemmas, one per row. Each is still `decide +kernel`, and `hBC` and `hXY` are then assembled from them by `ext` and `fin_cases`.
- **The statements of `hBC`, `hXY` and `rank_gram_map_five`, the whole general part of DL2 and both final theorems are byte-identical to Aristotle's.** Only the proofs of `hBC` and `hXY` changed. The complete diff against Aristotle's file is `DL2_split_m5.diff` (four hunks, all inside `namespace DL2.Five`); Aristotle's original is kept in `run2/`.
- With the split, the full `DL2.lean` builds in 86 s.

**Other incidents.**
- DL1: the build and the checks passed on the first run.
- DL2: before the split, the general part (everything except `namespace DL2.Five`) was certified on its own (`checks_lean/DL2_general_only.lean`, Aristotle's text verbatim up to that namespace), 149 s, axioms standard.
- DL3: no kernel evaluation of its own; built in 29 s.

---

## 6. Data per piece

| # | Aristotle task | Tarball | md5 | Downloaded | Build (s) | Peak (GB) | Lines | Thms | Defs | Checks before sending |
|---|---|---|---|---|---|---|---|---|---|---|
| DL1 | `4bc5652a` | (8) | `42ae52ff` | 30 Sep 09:18 | 72 | 1.59 ¹ | 394 | 35 | 4 | `G Y G = 6m² G` exact at `m = 5, 7, 11, 13, 17`; control `G Y G = 6m·G` fails at all five; minimal polynomial `x(x+m)(x+2m)(x−3m)` at all five |
| DL2 | `f130f94c` | (9) | `429bc685` | 30 Sep 09:55 | 86 ² | 4.15 | 1079 ³ | 71 | 24 | `G = SᵀΓS − mI` at `m = 5, 7, 11, 13`; `dim im S = 12m − 18`; `dim(W ∩ W^⊥) = 18` at `7, 11, 13` and `16` at `5`; `rank(G mod m) = 26, 48, 96, 120`; control: three degree-4 pairings nonzero at `m = 5` |
| DL3 | `24f74a8c` | (10) | `11b808fe` | 30 Sep 10:42 | 29 | 3.54 | 415 | 15 | 2 | Smith profiles of `G` over `Z_(m)`: `{26,10,1}`, `{48,38,5}`, `{96,158,17}`, `{120,254,23}` at `m = 5, 7, 11, 13`; `9m − 7` divisors of valuation `≥ 4` (the kernel) in each case |

¹ Measured by the first watchdog, resident memory only; the later figures are the real footprint.
² With the `m = 5` certificates split (§5). Aristotle's unsplit file was stopped by the watchdog at 901 s.
³ Local file, with the split; Aristotle's file has 774 lines.

Tarballs: files `884019b5-ec06-4ff7-8a7b-8d8a1f18d0a1-aristotle (N).tar.gz`, extracted to `run1/`, `run2/`, `run3/`. Lines, theorems and definitions are counted as in [WM-Lean, §6].

---

## 7. Totals

| Quantity | Value |
|---|---|
| Pieces sent to Aristotle | 3 (one task each) |
| Lean files of the Double Ladder | 3 (`DL1`, `DL2`, `DL3`), on top of the 9 files of the Watermark |
| Lines of Lean | 1 888 (local; with Aristotle's unsplit `DL2`, 1 583) |
| Theorems and lemmas | 121 |
| Definitions | 30 |
| `sorry` / `admit` / added axioms / `native_decide` | 0 / 0 / 0 / 0 |
| Axioms of the two final theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Calendar time | 30 Sep 2026: first result downloaded 09:18 (DL1), last 10:42 (DL3); clean rebuild and final check the same day |
| Clean rebuild of the whole project (Watermark + Double Ladder, 11 modules) | exit 0, **333 s**, peak **4.14 GB** (`build_clean_all.log`). The log keeps only the last lines of the build output and the watchdog's closing line: the 11 project modules `Defs`, `W1`–`W7`, `DL1`–`DL3` each rebuilt, then «Build completed successfully (8036 jobs)». The command line itself is not in the log. The header `Main.lean` is not rebuilt because nothing imports it. |
| Final check after the clean rebuild | 121 s, peak 2.52 GB, axioms standard (`check_run3_clean.log`) |

---

## 8. Reproducibility

**Machine:** Apple Mac (arm64), 8 CPU cores, 8 GB of memory, macOS (Darwin 25.5.0). **Toolchain:** `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` = commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The same toolchain and Mathlib as [WM-Lean] and [CL-Lean].

**Commands**, from the project root:

```
lake exe cache get
lake build                                        # all files; exit 0
lake env lean <path>/checks_lean/CheckDLFinal.lean    # statements, axioms, D, Y, non-vacuity
lake env lean <path>/checks_lean/DepsDL.lean          # the dependency cone
```

**Memory.** Loading Mathlib alone takes about 3 GB. The full build peaks at about 4.2 GB, in `DL2.lean`. A machine with 8 GB builds it; with less, expect swapping.

**Fingerprints of the source** (the 12 `.lean` files of the project). They were computed on 30 September, after the final check, on the files that were built; the build and check logs themselves do not record them.
- SHA-256 of the concatenation, in sorted path order: `02ca3b3d8b06e9cc1a2dbd4827365bed630f30cbe1747eb7f8e064bde427f1aa`.
- SHA-256 of the list of individual SHA-256 lines (`shasum -a 256 $(find RequestProject -name '*.lean' | sort) | shasum -a 256`): `bb612c10e71963482901dff9ce489755a6cf855df4cceba241ec564951fcd8b0`.

| File | SHA-256 |
|---|---|
| `RequestProject/DoubleLadder/DL1.lean` | `4572065d4a5f25a147c94bca0dc9ad01f33bd848775946280ce6e794079bb707` |
| `RequestProject/DoubleLadder/DL2.lean` | `7e7173b87edbd78e4f2b5273caa17c50988145f7b21eca9d05606af8f5ddc695` |
| `RequestProject/DoubleLadder/DL3.lean` | `17bf23320835c2ee9c4b07e8bd36024b9c7ad8fe0c8986f814572633ac1925a4` |
| `RequestProject/Main.lean` | `929b0bddef0b781f3fb42c7a99f252dc0bda7331f698104f7075e12ff637c52d` |
| `RequestProject/Watermark/Defs.lean` | `0af5ba018edd1a64138a40349e3d448062cdb20dbb5c2634198f47ff19af12b5` |
| `RequestProject/Watermark/W1.lean` | `fe5a814f4feba342697dd66dcaa9d95d403a06d4e458afc9014e08664649075a` |
| `RequestProject/Watermark/W2.lean` | `29580b50a72a8b11bf02c2f622198e632ff92b0df4386ebe4fd5dc46395c9342` |
| `RequestProject/Watermark/W3.lean` | `61a2e26993834c755c580c39dd01b0b936f5657eeef8f88c4c4208a9ffbefbd7` |
| `RequestProject/Watermark/W4.lean` | `a2419a27d3bf7d6c14e94135258f51271142b7049695ed379c84e78553077a06` |
| `RequestProject/Watermark/W5.lean` | `05a5311a1761f00fc1c260548d0d6f43a981384abe286a59f1ec3a2d42eb4858` |
| `RequestProject/Watermark/W6.lean` | `f0fbd352eee1f075ec7640643fe68b0eb8303ef4404be7a4155644309b734839` |
| `RequestProject/Watermark/W7.lean` | `bc93a6455c604248ebfa186150b7f6eb66662c0c65c4ad1738df8d499f473a58` |

The nine Watermark rows are identical to [WM-Lean, §8].

**On the author's machine** (folder `ARISTOTLE_LEAN/DOUBLE_LADDER/` of the author's archive; the Lean project itself is `ARISTOTLE_LEAN/WATERMARK/proyecto/`): the three pieces; `run1/`–`run3/`; the brute-force scripts and logs in `checks/`; the Lean check files in `checks_lean/`; every build and check log; `DL2_split_m5.diff`; the state file `ESTADO_DOUBLE_LADDER.md`; and the pencil proof [DL-Pencil]. **Where the files are published:** the repository `github.com/tretoef-estrella/watermark-theorem`, folder `lean/`; the project is `lean/project/`, and everything listed here is in `lean/double-ladder/`, with the same names and relative paths (the returned projects `run1/`–`run3/` are not published, and neither is one empty log of the interrupted build).

**Recommended to a reader who wants to remove the remaining trust in the author's logs:** an independent `lake build` on another machine, and a run of `lean4checker`. Neither has been done yet.

---

## 9. What was known before

This section records what we found in the literature on 30 September 2026. A search cannot prove that nothing exists; it records what we looked at. Sources read in the original are marked «read».

- **Shioda (1987)** [Sh87], read (Project Euclid, 17 pages). §7, p. 133. *Question 7.2*: for the Fermat surface of prime degree `m` in characteristic `p ≡ 1 (mod m)`, is `|det NS(X)| = m^{3(m−3)²}`? *Question 7.4 (i)*: for the complex Fermat surface of prime degree `m`, are (7.10) `|det NS| = m^{3(m−3)²}` and (7.11) «`NS` is spanned by the classes of lines» true? He asks for the determinant, not for the group. «Added in proof» (1): the discriminant divides a power of `m` for every `m`. The Watermark Theorem answers (7.10) for every prime `m ≥ 5`, and [Deg] answers (7.11). The Double Ladder Theorem goes beyond the question: it gives the group, not only its order.
- **Schütt, Shioda, van Luijk (2010)** [SSvL], read (arXiv source, dated 30 Sep 2009). End of §4: for every odd `m ≤ 81`, the determinant of the intersection form of the lines of their basis `𝓑` is `m^{3(m−3)²}`, «with exponent as conjectured in [Sh87]». They prove that the lines span `NS ⊗ Q`, and span `NS` for `m ≤ 100`, `gcd(m, 6) = 1`. They give the determinant, not the group.
- **Degtyarev (2015)** [Deg], read (arXiv source). For every `m ≤ 4` or `gcd(m, 6) = 1`, the lines generate `NS(S_m)` over `Z`. The proof is topological; it gives no discriminant.
- **Shioda (2015)** [Sh15], read. In §6.5, Conjecture 23, for `m` prime to `6`, he writes `det NS(X_m) = m^{3(m−3)²}` inside a conjecture on Mordell–Weil lattices. So in 2015 the formula was still used as expected, not as proved.
- **Aljovin, Movasati, Villaflor (2019)** [AMV], read. Table 1 lists, by machine (Smith normal form, one cell at a time), the elementary divisors of the lattice of linear cycles of the Fermat surface for `3 ≤ m ≤ 14`. The rows for prime `m` are:
  - `(2,5)`: `1^{26} · 5^{10} · 25` — that is, `(Z/5)^{10} × Z/25`;
  - `(2,7)`: `1^{48} · 7^{38} · 49^{5}`;
  - `(2,11)`: `1^{96} · 11^{158} · 121^{17}`;
  - `(2,13)`: `1^{120} · 13^{254} · 169^{23}`.

  All four agree with the Double Ladder Theorem. [AMV] give no general formula and no proof for general `m`. (Their sign column reads `−` for `(2,7)`. For the lattice of the lines, Lean proves the sign `+` (the Watermark), as the Hodge index theorem predicts: the rank minus one, `90`, is even. The sign does not affect the group.)
- **Jumagulov (2026)** [Jum], read: Galois-invariant Néron–Severi ranks of Fermat surfaces; no discriminant.
- **Also screened:** the 51 works that Semantic Scholar lists as citing [SSvL] (titles and, where relevant, abstracts), and web searches for the formula, for the discriminant group of `NS` of Fermat surfaces, and for its elementary divisors. We found no general formula for the discriminant group, and no proof of the determinant formula, before June 2026.

**Therefore.** Before this work, the determinant `m^{3(m−3)²}` was conjectured (Shioda) and checked by computer for odd `m ≤ 81` [SSvL]; the discriminant group was known by computer for `m ≤ 14` [AMV]. As far as we could determine, a formula for all primes and its proof are new: the Watermark Theorem (the order) and the Double Ladder Theorem (the structure). Both are now certified in Lean for every prime `m ≥ 5`.

**Three corrections to earlier texts, found while writing this section.**
1. *The Double Ladder Theorem* v2 (§1 and §9) says that the `m = 11` profile lies «outside every published table» and that [AMV] supplies two of its three anchors. In fact [AMV, Table 1] lists all three, `m = 5, 7, 11`, and also `m = 13`. The `m = 11` value was indeed predicted before it was computed, but it was not new. The theorem is unaffected.
2. The pencil proof, version 1 (§5 and §6), calls `m = 13` «a new cell». It is row `(2,13)` of [AMV]. Version 2 [DL-Pencil] corrects it.

3. *The Double Ladder Theorem* v2 (Abstract and §1) says that Shioda asked for the determinant «and, behind it, the discriminant form», and that the two theorems answer his Question 7.4 «in full … not only the determinant … but its discriminant form's underlying group». [Sh87] asks only for the determinant (Questions 7.2 and 7.4). The Watermark answers (7.10); the Double Ladder goes further.

---

## 10. What this certificate claims, in one paragraph

A computer proof assistant, Lean 4 with the Mathlib library, has checked a complete proof of the following statement, with no gap and no axiom beyond the three standard ones:

> Let `G` be the explicit `3m² × 3m²` integer matrix of [WM-Lean, §1.2], `V = Z^{3m²}/ker G` with the form induced by `G`, and `V* = Hom(V, Z)`. For every prime `m ≥ 7`, `V*/V ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}`; and `V*/V ≅ (Z/5)^{10} × Z/25` for `m = 5`.

`G` is the intersection matrix of the `3m²` lines on the Fermat surface `S_m` ([WM-Lean, §1.4]: proved by hand, checked by computer, not formalized), and by [SSvL] and [Deg] `V = NS(S_m)` for prime `m`. The statement is therefore the structure of the discriminant group of the Néron–Severi lattice of the Fermat surface of every prime degree `m ≥ 5`. Together with the Watermark Theorem, certified in [WM-Lean], it gives the complete elementary-divisor profile of that lattice.

The proofs in Lean were written by the AI system Aristotle (Harmonic) from pieces written by the author. The author's audit, assisted by Claude (Anthropic), checked that the statements match the paper, and compiled and re-checked everything on his own machine.

## 11. Changes from v1, after the cold read

An independent reader, with no access to the author's archive, audited v1 against the Lean sources, the logs, the paper and the cited sources (30 September 2026). Verdict: **the certificate holds; no fatal error and no gap.** The reader re-derived the matrix `G` from the lines of the Fermat surface (zero disagreements at `m = 5, 7`), checked both `m = 5` certificates, recomputed the Smith profiles at `m = 5, 7, 11`, and recounted every fingerprint and number. The corrections made in v2:

- **Four wrong statements, now corrected:**
  1. The paper's own proof has four steps confirmed only numerically, not one (§0).
  2. The paper was named as «v2, the highest version» (header, §1.3, references). Version 4 is the published one, and the Watermark certificate is cited as v2.
  3. Lean identifies the relations by mixed second differences, not by polynomials of degree `≤ m − 1` (§3.1, step 3).
  4. `G` does not act diagonally on the overlap pullbacks. It mixes each pair, and Lean treats the pair jointly (§3.1, step 2).
- **Unclear wording, now made precise:**
  - how many intermediate theorems the final check prints, and the axioms of which of them (§1);
  - that the two `m = 5` cone counts are differences of counts (§3.2);
  - that the 9 GB figure is an estimate (§5);
  - what the clean-rebuild log contains (§7);
  - that the logs do not record the fingerprints (§8);
  - how the Lean proof differs in detail from the pencil proof (§2).
- **Three further points concern the pencil proof,** now in its version 2 [DL-Pencil]:
  - its status line;
  - the unit binomial coefficients behind the independence in Lemma 3.1;
  - the passage from the Smith form of `G` to `V*/V`.
- **One concerns the paper:** its Abstract read as a complete proof. Version 4 says which proof is complete.

## References

- [AMV] E. Aljovin, H. Movasati, R. Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184; arXiv:1711.02628.
- [CL-Lean] R. Amichis Luengo, *The Chaise Longue Theorem — Lean Certificate*, v1, Zenodo 2026, DOI 10.5281/zenodo.23045371.
- [Deg] A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477; arXiv:1305.3073.
- [Jum] R. Jumagulov, *Galois-invariant Néron–Severi ranks of Fermat surfaces over number fields*, arXiv:2607.17387 (2026).
- [Nik] V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Math. USSR Izv. **14** (1980), 103–167.
- [Sh87] T. Shioda, *Some observations on Jacobi sums*, in: Galois Representations and Arithmetic Algebraic Geometry, Adv. Stud. Pure Math. **12** (1987), 119–135; doi:10.2969/aspm/01210119.
- [Sh15] T. Shioda, *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, J. Math. Sci. Univ. Tokyo **22** (2015), 443–468.
- [SSvL] M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), 1939–1963; arXiv:0812.2377.
- [DL-Pencil] R. Amichis Luengo (written with Claude), *The Double Ladder Theorem — a pencil proof*, version 2, 30 September 2026; repository `watermark-theorem`, `lean/double-ladder/THE_DOUBLE_LADDER_PENCIL_PROOF_v2.md`.
- [WM-Lean] R. Amichis Luengo, *The Watermark Theorem — Lean Certificate*, v2, 30 September 2026; repository `watermark-theorem`, `lean/watermark/`.
- R. Amichis Luengo, *The Double Ladder Theorem*, 5 June 2026, version 4 of 30 September 2026; repositories `chaise-longue-theorem` (`hodge-fermat-campaign/`) and `watermark-theorem` (`papers/`).
- The Lean 4 theorem prover, https://lean-lang.org; the Mathlib library, https://github.com/leanprover-community/mathlib4.
- Aristotle, Harmonic, https://aristotle.harmonic.fun.

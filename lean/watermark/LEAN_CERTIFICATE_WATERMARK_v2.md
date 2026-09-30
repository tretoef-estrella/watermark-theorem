# THE WATERMARK THEOREM — LEAN CERTIFICATE
## A machine-checked proof, in Lean 4 with Mathlib, that the lattice of the lines on the Fermat surface of prime degree `m ≥ 5` has discriminant `m^{3(m−3)²}`

**Rafael Amichis Luengo** · Madrid, Spain · tretoef@gmail.com

Certificate v2 · 30 September 2026. v2 adds §10 (what was known before, from the sources read in the original), states Shioda's 1987 question exactly, and points to the Double Ladder certificate. The Lean content, the numbers and the fingerprints of v1 are unchanged.

Companion to *The Watermark Theorem* (R. Amichis Luengo, 4 June 2026), file `hodge-fermat-campaign/THE_WATERMARK_THEOREM.md` of the repository `github.com/tretoef-estrella/chaise-longue-theorem`, and `papers/THE_WATERMARK_THEOREM.md` of `github.com/tretoef-estrella/watermark-theorem`. The Lean project and all the evidence are in the second repository, folder `lean/`.

---

## 0. Verdict

For every prime `m ≥ 5`, Lean 4 proves the following about the lattice `V` spanned by the `3m²` lines of the Fermat surface of degree `m`, with the bilinear form given by their intersection numbers:

- `V` is a **free abelian group of rank `3(m−1)(m−2) + 1`**;
- for **every** `Z`-basis `b` of `V`, the determinant of the Gram matrix of `b` is **exactly `m^{3(m−3)²}`**, with sign `+`.

The paper states `|disc V| = m^{3(m−3)²}` and gives the sign separately. Lean proves the value with its sign. The determinant does not depend on the basis.

For prime `m`, Shioda asked in 1987 whether `|det NS| = m^{3(m−3)²}` ([Sh87], Questions 7.2 and 7.4, p. 133); [SSvL, §4] calls the formula his conjecture. Schütt, Shioda and van Luijk checked it by computer for every odd `m ≤ 81` [SSvL]. Aljovin, Movasati and Villaflor listed, by computer, the elementary divisors of this lattice for `m ≤ 14` [AMV, Table 1]. In 2015 Shioda still used the formula inside a conjecture [Sh15, Conjecture 23]. As far as we know no proof existed before June 2026. §10 gives the sources, read in the original.

The same Lean project also proves the **Double Ladder Theorem**, the structure of the discriminant group `V*/V`, on top of this one; see its certificate [DL-Lean].

The whole proof compiles on the author's Mac. It contains no `sorry`, no `admit`, no `native_decide`, no `decide` and no added axiom. The final theorem depends only on the three standard axioms of Lean and Mathlib: `propext`, `Classical.choice` and `Quot.sound`.

**What Lean certifies, and what it does not.** Lean works with an explicit integer matrix `G` of size `3m² × 3m²` (§1.2). That `G` is the matrix of intersection numbers of the lines on the complex Fermat surface is geometry. It is proved by hand in §1.4, by solving linear equations, and checked by computer for `m = 5, 7, 11`. It is not formalized. Two further facts are cited, not formalized: that `A/ker G` is the lattice of lines inside `H²(S_m, Z)`, and that for prime `m` this lattice is the whole Néron–Severi group [SSvL, Deg]. So:

> **Lean certifies the lattice statement completely. The statement about the Fermat surface follows from it by the identification of §1.4, proved by hand and checked by computer, and by the cited results of [SSvL] and [Deg].**

§1 states exactly what is proved. §2 states exactly what is not. §3–§8 describe how the result was obtained and how to check it. §9 says in one paragraph what is claimed; §10 records what was known before.

---

## 1. The certified statement

### 1.1 The theorem, verbatim

Printed by Lean with `#check` (logs `check_run7.log` and `checkfinal.log`):

```
@watermark_theorem : ∀ {m : ℕ} [inst : Fact (Nat.Prime m)],
  5 ≤ m →
    Module.Free ℤ (V m) ∧
      Module.finrank ℤ (V m) = 3 * (m - 1) * (m - 2) + 1 ∧
        ∀ {ι : Type u_1} [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (b : Module.Basis ι ℤ (V m)),
          ((LinearMap.BilinForm.toMatrix b) (formV m)).det = ↑m ^ (3 * (m - 3) ^ 2)
```

```
'Watermark.watermark_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The basis `b` may be indexed by any finite type in any universe.

### 1.2 The definitions it uses, verbatim

These are all the definitions needed to read the statement. They are printed by `#print` in `checkfinal.log`. All of them are in the file `RequestProject/Watermark/Defs.lean` (188 lines), written in the first piece and never changed afterwards.

```
@[reducible] def Watermark.Point : ℕ → Type :=
fun m => ZMod m × ZMod m

@[reducible] def Watermark.Line : ℕ → Type :=
fun m => Fin 3 × Point m

def Watermark.gramUpper : (m : ℕ) → Line m → Line m → ℤ :=
fun m p q =>
  if p.1 = q.1 then if p.2 = q.2 then 2 - ↑m else if p.2.1 = q.2.1 ∨ p.2.2 = q.2.2 then 1 else 0
  else
    if p.1 = 0 ∧ q.1 = 1 then if p.2.1 - p.2.2 = q.2.1 - q.2.2 then 1 else 0
    else
      if p.1 = 1 ∧ q.1 = 2 then if p.2.1 + p.2.2 = q.2.1 + q.2.2 then 1 else 0
      else if p.1 = 0 ∧ q.1 = 2 then if q.2.1 - q.2.2 = p.2.1 + p.2.2 + 1 then 1 else 0 else 0

def Watermark.gram : (m : ℕ) → Matrix (Line m) (Line m) ℤ :=
fun m => Matrix.of fun p q => if p.1 ≤ q.1 then gramUpper m p q else gramUpper m q p

@[reducible] def Watermark.A : ℕ → Type :=
fun m => Line m → ℤ

def Watermark.gramLin : (m : ℕ) → [NeZero m] → A m →ₗ[ℤ] A m :=
fun m [NeZero m] => (gram m).mulVecLin

def Watermark.K : (m : ℕ) → [NeZero m] → Submodule ℤ (A m) :=
fun m [NeZero m] => (gramLin m).ker

@[reducible] def Watermark.V : (m : ℕ) → [NeZero m] → Type :=
fun m [NeZero m] => A m ⧸ K m

def Watermark.gramForm : (m : ℕ) → [NeZero m] → LinearMap.BilinForm ℤ (A m) :=
fun m [NeZero m] => (Matrix.toLinearMap₂' ℤ) (gram m)

def Watermark.gramFormAux : (m : ℕ) → [inst : NeZero m] → V m →ₗ[ℤ] A m →ₗ[ℤ] ℤ :=
fun m [NeZero m] => (K m).liftQ (gramForm m).flip ⋯

def Watermark.formV : (m : ℕ) → [inst : NeZero m] → LinearMap.BilinForm ℤ (V m) :=
fun m [NeZero m] => (K m).liftQ (gramFormAux m).flip ⋯
```

The two `⋯` are proof terms: that `gramForm` vanishes when one argument lies in `K`, so that it descends to the quotient. Lean checks them; they carry no data. By the lemma `formV_mk`, `formV [x] [y] = x ⬝ G ⬝ y` for all `x, y ∈ A`.

### 1.3 Faithfulness to the paper, line by line

The paper is *The Watermark Theorem*, v1.0 of 4 June 2026, §2.

| Paper | Lean | Agreement |
|---|---|---|
| the `3m²` lines, three families of `m²`, each indexed by `(k, l) ∈ (Z/m)²` | `Line m = Fin 3 × ZMod m × ZMod m` | Identical. Families 1, 2, 3 of the paper are `j = 0, 1, 2`. |
| self-intersection `2 − m` | `p = q` gives `2 − ↑m` | Identical. |
| same family: `1` iff `k = k′` or `l = l′`, for distinct lines | `p.2.1 = q.2.1 ∨ p.2.2 = q.2.2` gives `1`, else `0` | Identical. |
| family 1 × family 2: `k − l ≡ k′ − l′` | case `p.1 = 0 ∧ q.1 = 1` | Identical. |
| family 2 × family 3: `k + l ≡ k′ + l′` | case `p.1 = 1 ∧ q.1 = 2` | Identical. |
| family 1 × family 3: `k′ − l′ ≡ k + l + 1`, with `(k′, l′)` in family 3 | case `p.1 = 0 ∧ q.1 = 2`: `q.2.1 − q.2.2 = p.2.1 + p.2.2 + 1` | Identical; `q` is the line of family 3. |
| the lower blocks by symmetry | `gram` reads `gramUpper` with the arguments swapped when `p.1 > q.1` | Identical. `gram_transpose` proves `Gᵀ = G`. |
| `A = ⊕_j Z^{(Z/m)²}`, `G` the Gram matrix | `A m = Line m → ℤ`, `gram m` | Identical. |
| `V` := the lattice spanned by the classes of the lines | `V m = A m ⧸ ker G` with the form induced by `G` | The same lattice: see §1.4, point 3. |
| `m ≥ 5` prime | `[Fact (Nat.Prime m)]`, `5 ≤ m` | Identical, and no other hypothesis. |
| `rank V = 3(m − 1)(m − 2) + 1` | `Module.finrank ℤ (V m) = 3 * (m - 1) * (m - 2) + 1` | Identical. The subtraction in `ℕ` never truncates, because `m ≥ 5`. |
| `\|disc V\| = m^{3(m−3)²}`, and `disc V = (−1)^{rank V − 1}\|disc V\|` | `det (toMatrix b (formV m)) = m ^ (3 * (m - 3) ^ 2)` for every basis `b` | Lean proves the value with its sign. The sign `+` agrees with the paper, because `rank V − 1 = 3(m − 1)(m − 2)` is even. |

**Non-vacuity.**

- «Free of rank `r`» is stated as `Module.Free ℤ (V m) ∧ Module.finrank ℤ (V m) = r`. In Mathlib the rank of a module that is not finitely generated is `0`. Here `r = 3(m−1)(m−2)+1 ≥ 37`, so the statement forces `V m ≅ Z^r`.
- The clause «for every basis» is therefore not empty. This is also checked in Lean on an instance: the file `checks/CheckFinal.lean` proves, from the theorem, that at `m = 5` a `Z`-basis of `V 5` exists, has `37` elements, and has Gram determinant `5^{12}`. It compiles with no error (`checkfinal.log`).
- The hypotheses can be satisfied: `m = 5` is used in that check.

### 1.4 The matrix is the geometry

This part is **not** formalized. It connects the matrix `G` of §1.2 to the Fermat surface `S_m : x₀^m + x₁^m + x₂^m + x₃^m = 0` in `P³(C)`.

**1. The lines.** Put `ε = e^{πi/m}` and `ζ = e^{2πi/m}`, so that `ε^m = −1`. For `a, b ∈ Z/m`, the following three kinds of line lie on `S_m`:
- family 1: `x₀ = εζ^a x₁`, `x₂ = εζ^b x₃`;
- family 2: `x₀ = εζ^a x₂`, `x₁ = εζ^b x₃`;
- family 3: `x₀ = εζ^a x₃`, `x₁ = εζ^b x₂`.

For example, on a line of family 1, `x₀^m + x₁^m = (ε^m + 1)x₁^m = 0` and likewise `x₂^m + x₃^m = 0`. These are the `3m²` lines of `S_m` [SSvL]. The line with parameters `(a, b)` in family `f` corresponds to the Lean index `(f − 1, (a, b))`.

**2. The intersection numbers.**
- A line has self-intersection `2 − m`: by adjunction, `L² = −2 − K·L` and `K = (m − 4)H`.
- Two distinct lines meet transversally in at most one point, so their intersection number is `1` if they meet and `0` if not.
- They meet exactly when their four linear equations have a common non-zero solution. Solving the four equations gives:
  - same family: they meet iff they share `a` or share `b`;
  - families 1 and 2, with parameters `(a, b)` and `(c, d)`: iff `εζ^a · εζ^{d} = εζ^b · εζ^{c}`, i.e. `a − b ≡ c − d`;
  - families 2 and 3, with `(c, d)` and `(e, f)`: iff `c + d ≡ e + f`;
  - families 1 and 3, with `(a, b)` and `(e, f)`: from `x₀ = εζ^a x₁ = εζ^a εζ^f x₂ = εζ^a εζ^f εζ^b x₃ = εζ^e x₃` one gets `ε²ζ^{a+b+f} = ζ^e`, and `ε² = ζ`. So they meet iff `e − f ≡ a + b + 1`.

These are exactly the six cases of `gramUpper`. The `+1` of the last case is `ε² = ζ`.

**3. The lattice.**
- `H²(S_m, Z)` is torsion free and its intersection form is unimodular.
- The classes of the lines span `NS(S_m) ⊗ Q` if and only if `m ≤ 4` or `gcd(m, 6) = 1`: a theorem of Shioda, recalled in [SSvL, §3]. This covers every prime `m ≥ 5`.
- The intersection form on `NS(S_m)` is non-degenerate (Hodge index).

So a combination `x ∈ A` of lines has class `0` if and only if it pairs to zero with every line, that is, if and only if `Gx = 0`. Hence the lattice spanned by the lines, with its intersection form, is `A/ker G` with the form induced by `G`. This is `V m` with `formV m`.

**4. Computer check.** The script `checks/wfinal_geometry.py` builds the three families of lines numerically and decides, for every pair, whether the four equations have a common non-zero solution (rank of a `4 × 4` complex matrix). It compares the result with a verbatim transcription of `gramUpper`.
- `m = 5, 7, 11`: all 2 850, 10 878 and 66 066 pairs agree.
- **Control:** the same comparison with `k + l − 1` in place of `k + l + 1` in the last case disagrees on 250, 686 and 2 662 pairs.

Log: `checks/wfinal_geometry.log`.

**5. The Néron–Severi group.** For `gcd(m, 6) = 1` the lines generate `NS(S_m)` over `Z`: [SSvL] for `m ≤ 100`, and [Deg] for every such `m`. So for every prime `m ≥ 5`, `V = NS(S_m)` and the theorem gives `disc NS(S_m) = m^{3(m−3)²}`. This is cited, not formalized.

### 1.5 The main intermediate theorems

Each is printed in the check log of its run, with axioms `[propext, Classical.choice, Quot.sound]`.

- `SAT_le_K` (W3): the explicit sublattice `SAT` lies in `ker G`, **for every `m ≥ 1`**. The paper records the corresponding membership (§7 there) as verified by computer only; Lean proves it for every `m`.
- `finrank_ker_satMap = 12` and `finrank_range_satMap = 9m − 19` (W2): Lemma C of the paper, the relation count modulo `m`.
- `finrank_SAT = 9m − 7` for odd `m` (W3), and `finrank_K = 9m − 7` for prime `m ≥ 5` (W5).
- `smul_mem_SAT` (W5): `m·x ∈ SAT` for every `x ∈ ker G`, with an explicit witness.
- `index_SAT` (W5): `[K : SAT] = m^{12}`.
- `index_Lfam` (W6): the lattice of pencil pullbacks on one family has index `m^{(m²+m+2)/2}` in `Z^{m²}`, for every prime `m`.
- `F_inf_K`, `finrank_F`, `index_F_sup_K` (W6): the sublattice `F` meets `ker G` in `0`, has rank `3(m−1)(m−2)+1`, and `[A : F + K] = m^{3(m²+m+2)/2 − 12}`.
- `V_free` (W7): `V m` is free for **every** `m ≥ 1`.

---

## 2. What is not certified

1. **The geometry of §1.4.**
   - That `G` is the intersection matrix of the lines on `S_m`: proved by hand in §1.4 and checked by computer at `m = 5, 7, 11`, not formalized.
   - That `A/ker G` is the lattice of lines in `H²(S_m, Z)`: standard facts, cited.

   Mathlib has no complex algebraic surfaces and no singular cohomology of them.
2. **The equality `V = NS(S_m)`** for prime `m`: [SSvL] and [Deg], cited. With it, the theorem computes `disc NS(S_m)`.
3. **The paper's own proof is not the proof formalized.**
   - The paper proves the theorem through characters of `(Z/m)³`, trace lattices and a large determinant (§§3–10 there).
   - Lean follows a different route, entirely over the integers and without characters (§3.1 below). It was designed for the formalization and checked numerically before each piece was sent.
   - The Lean proof is therefore a second, independent proof of the same statement. It will be written as a paper in a later version.
4. **Not formalized, and not claimed here:**
   - odd composite `m` and even `m`, where the formula is conjectural (paper §2);
   - the corollaries of the paper's §12: the transcendental lattice and the Brauer group;
   - *The Double Ladder Theorem* (the group structure of `V*/V`).
5. **Faithfulness is an audit, not a theorem.**
   - Lean guarantees that the proof is correct for the statement as written. That the statement says what the paper says is checked in §1.3.
   - A reader should check §1.2–§1.3 independently: one short file, `Defs.lean`, and six cases of `gramUpper`. This is the one place where trust in the author remains, together with the geometry of §1.4.
6. **Timing data.** Aristotle's own start and end times per task were not exported. The times in §6 are the download times of the result files: an upper bound for completion, not a measure of Aristotle's work.

---

## 3. How the proof is organised in Lean

The proof was cut into seven pieces, W1–W7. Each piece is one self-contained Markdown file in `pieces/`, with Setting, Statements, Proof and Checks. Each piece produced one Lean file in `RequestProject/Watermark/`.

No piece ever modified a file of an earlier piece. Every returned project was compared file by file with the compiled project, and all earlier `.lean` files were byte-identical, as were `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`.

| # | Piece | Content | Lean file | Main Lean results |
|---|---|---|---|---|
| W1 | `w1_gram_basics.md` | lines, `G`, `A`, `K = ker G`, `V`, the induced form; `Gᵀ = G`; `G·N_j = m·𝟙`; R.1; R.2 | `Defs.lean`, `W1.lean` | `gram_transpose`, `gram_mulVec_famVec`, `sum_E_pencil`, `aug_of_mem_K`, `formV`, `formV_isSymm` |
| W2 | `w2_counting_lemma.md` | the sublattice `SAT` (nine sum-zero functions and two scalars); Lemma C: kernel `12`, range `9m − 19` | `W2.lean` | `SAT`, `finrank_satSrc`, `exists_satSrc_lift`, `finrank_ker_satMap`, `finrank_range_satMap` |
| W3 | `w3_sat_in_K.md` | `SAT ⊆ K` for every `m`; injectivity and rank `9m − 7` for odd `m` | `W3.lean` | `gram_mulVec_satMap`, `SAT_le_K`, `satMap_injOn`, `finrank_SAT` |
| W4 | `w4_pencil_calculus.md` | pullbacks along the `m + 1` pencils; `G` on pullbacks: `0` on axis pencils, `−m` on live pencils, six overlap formulas | `W4.lean` | `pb`, `fib`, `gram_mulVec_pb_live`, the six `gram_mulVec_pb_*` overlap formulas, `sum_pencil_mul_pencil`, `smul_ext_eq_sum_pb_fib` |
| W5 | `w5_mK_in_SAT.md` | the census of `ker G`; `m·K ⊆ SAT`; `rank K = 9m − 7`; `[K : SAT] = m^{12}` | `W5.lean` | `fib_live_const`, `fib_overlap_*`, `smul_mem_SAT`, `finrank_K`, `index_SAT` |
| W6 | `w6_index.md` | the sublattice `F`, its Gram matrix, `F ∩ K = 0`, `[Z^{m²} : L_j] = m^{(m²+m+2)/2}`, `F + SAT = L`, `[A : F + K]` | `W6.lean` | `gramForm_pb_pb_of_ne`, `gramForm_pb_pb_self`, `gramForm_famVec_self`, `F_inf_K`, `finrank_F`, `index_Lfam`, `F_sup_SAT`, `index_F_sup_K` |
| W7 | `w7_discriminant.md` | `V` free of rank `3(m−1)(m−2)+1`; the Gram determinant of `F`; change of basis | `W7.lean` | `V_free`, `finrank_V`, `det_gramC`, `index_map_F`, `exponent_eq`, `watermark_theorem` |

### 3.1 The chain of the final theorem

This is how `watermark_theorem` is proved in Lean. Every step is a Lean proof. Write `pb_j^π(u)` for the pullback of a function `u : Z/m → Z` to family `j` along the pencil `π`, and `Z₀` for the functions with sum `0`.

1. **Freeness and rank** (W7, `V_free`, `finrank_V`). `V = A/ker G` is torsion free: if `c·x ∈ ker G` with `c ≠ 0`, then `x ∈ ker G`. It is finitely generated, hence free. Its rank is `3m² − rank K = 3m² − (9m − 7) = 3(m−1)(m−2) + 1`. The value `rank K = 9m − 7` comes from W5.
2. **`G` on pullbacks** (W4). For `u ∈ Z₀`:
   - `G·pb^π(u) = 0` on the two axis pencils;
   - `G·pb^π(u) = −m·pb^π(u)` on the `m − 3` live pencils `t ∉ {0, ±1}`;
   - on the six pencils `±1` (two per family), `G·pb^π(u) = −m·pb^π(u) + m·pb^{π′}(u′)`, with `π′` a pencil `±1` of another family, `u′ = u` for the pairs of families `(1,2)` and `(2,3)`, and `u(x − 1)` or `u(x + 1)` for the pair `(1,3)`.
3. **The kernel and `SAT`** (W2, W3, W5).
   - `SAT ⊆ K` for every `m` (W3).
   - Pairing `x ∈ K` against pullbacks gives the census: the fibre sums of `x` along the live pencils are constant, and so are the differences along the overlap pencils (W5).
   - From the census one builds an explicit admissible datum `D` with `satMap(D) = m·x`, so `m·K ⊆ SAT` (W5).
   - With Lemma C (W2: kernel `12` modulo `m`) and `K ∩ m·A = m·K` (`K` is saturated), this gives `[K : SAT] = m^{12}` (W5).
4. **The sublattice `F` and its index** (W6).
   - `F` is spanned by the blocks `pb_j^t(Z₀)` for the `3(m − 3)` live pencils, one member of each of the three overlap pairs, and `N₀`.
   - By step 2, distinct blocks are `B`-orthogonal, `B(pb u, pb v) = −m²Σ u(x)v(x)` inside a block, and `B(N₀, N₀) = m³`. Positivity of `Σu²` then gives `F ∩ K = 0`.
   - `F + SAT = L`, where `L` is the lattice of vectors whose restriction to each family lies in `L_j` = span of `1` and all pencil pullbacks. The standard Gram matrix of `L_j` is block diagonal, so `[Z^{m²} : L_j] = m^{(m²+m+2)/2}`.
   - Since `F ∩ K = 0`, `[F + K : F + SAT] = [K : SAT] = m^{12}`, and so `[A : F + K] = m^{3(m²+m+2)/2 − 12}`.
5. **The determinant** (W7).
   - The images in `V` of the spanning vectors of `F` are linearly independent. Their Gram matrix is block diagonal: `3(m − 2)` blocks `−m²(I + J)` of size `m − 1` and one block `m³`. Its determinant is `m^{3(m−2)(2m−1)+3}`, with sign `+` because `m − 1` is even.
   - They span a sublattice of `V` of index `[A : F + K]`. By `Submodule.natAbs_det_basis_change` in Mathlib and the change-of-basis formula `Gram_c = Pᵀ Gram_b P`:
     `det Gram_b = m^{3(m−2)(2m−1)+3} / m^{2(3(m²+m+2)/2 − 12)} = m^{3(m−3)²}`.
   - A basis indexed by any other finite type is reindexed; the determinant does not change.

### 3.2 The dependency cone

A short Lean program (`checks/DepsFinal.lean`, log `deps_watermark.log`) collects every declaration that `watermark_theorem` uses, directly or indirectly, and keeps those defined in the project.

- **Size:** **410** declarations of the project, in **8** of its 9 files: `Defs` 36, `W1` 34, `W2` 81, `W3` 38, `W4` 24, `W5` 50, `W6` 103, `W7` 44. Every one of them is checked by the kernel as part of `watermark_theorem`.
- The only file not in the cone is `RequestProject/Main.lean`: 24 lines of options and no declaration, the default header of an Aristotle project. The Watermark files do not import it.

So every piece is on the path of the final theorem, as §3.1 says.

---

## 4. Trust base

- **What must be trusted:**
  - the Lean 4 kernel, toolchain `leanprover/lean4:v4.28.0`;
  - Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`, `lake-manifest.json`);
  - the three standard axioms `propext`, `Classical.choice`, `Quot.sound`;
  - the audit of the statement (§1.3) and the geometry of §1.4.
- **What need not be trusted:** Aristotle (Harmonic), the AI system that wrote the Lean proofs, and the author's brute-force checks. Every file Aristotle returned was compiled again on the author's machine, and the kernel re-checks every proof.
- **Forbidden constructs, searched as whole words in all 9 files:** none of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `csimp`, `partial`, `macro`, `elab`, `syntax`, `notation`, `debug` occurs.
- **The tactic `decide` does not occur**: the word `decide` is in none of the 9 files.
- **Options.** The eight Watermark files set **no option at all**, so they run with Lean's default resource limits. The 24-line file `Main.lean`, which is not imported, sets resource limits, printing options and `autoImplicit false`; none of them affects soundness.
- **Axioms of every main theorem**, printed after each piece (logs `check_run1.log` … `check_run7.log`): always `[propext, Classical.choice, Quot.sound]`.
- **Aristotle's own register** for the project lists 31 properties PROVED, 0 NEGATED, 0 in progress.

---

## 5. The procedure

The procedure is the one used for the Lean certificate of *The Chaise Longue Theorem* [CL-Lean]. For each of the seven pieces:

1. **Write the piece.** A self-contained Markdown file with Setting, Statements, Proof and Checks. It names the earlier Lean results it may reuse and forbids changing any existing file or statement.
2. **Brute-force check before sending.** A Python or Macaulay2 program checks the statements in small cases, with a negative control where possible (a deliberately wrong variant that must fail). The numbers are in the table of §6.
3. **Send to Aristotle** (project `884019b5-ec06-4ff7-8a7b-8d8a1f18d0a1`), one task per piece.
4. **Download** the resulting project (a `.tar.gz`), after reloading the project page and confirming that the task is finished, and extract it into `run<N>/`.
5. **Diff** against the locally compiled project. Stop if any earlier `.lean` file changed. None ever did.
6. **Grep** the new file for the forbidden constructs of §4.
7. **Build locally:** `lake build RequestProject.Watermark.W<N>` inside a watchdog that stops the build above 3 GB of memory or 15 minutes. Log `build_run<N>.log`.
8. **Print** the main statements (`#check`) and their axioms (`#print axioms`). Log `check_run<N>.log`.
9. **Audit faithfulness:** compare the printed statements with the piece and with the paper. Accept generalizations; stop on any weakening.
10. **Record** the run in the state file `ESTADO_WATERMARK.md`.

**Stop conditions, fixed in advance:**
- any property NEGATED by Aristotle;
- a statement that is not faithful;
- a build failure;
- a `sorry` or an extra axiom;
- a change to an old file.

**None occurred.**

**Incidents, recorded as they happened:**
- **W2.** The proof sketch in the piece contained an error: in the lift of a sum-zero function it subtracted `(Σ y₀)/m` where `Σ y₀` was needed. Aristotle noticed it and proved the statement with the correct lift. The statement was unaffected.
- **W3.** The author predicted that `SAT ⊆ K` would fail for even `m`. His own pre-send check refuted the prediction (it holds at `m = 4, 6`), and the piece was stated for every `m`. Injectivity does fail for even `m`, and that part is stated for odd `m`.
- **W4.** The first pre-send test of the overlap formulas had the direction of the translation wrong in the pair of families 1 and 3 (Lean indices `0` and `2`), and reported `False` (`checks/w4_route.log`). A diagnosis at `m = 5` found the right direction: `u(x − 1)` in `G·pb_0^{+1}` and `u(x + 1)` in `G·pb_2^{−1}`. The piece was sent with it. The corrected formulas were re-checked on 30 September at `m = 5, 7, 11` on a basis of `Z₀`: all true, and the swapped direction fails (`checks/w4_formulas_recheck.log`).
- **W5.** One download was premature: tarball `(4)` contains the state after W4, taken before W5 had finished. It was not used. Since then the project page is reloaded and the finished task confirmed before every download.

Several pieces were proved in a more general form than asked, and each is noted in the state file:
- unused hypotheses dropped: `SAT ⊆ K` for every `m`, `V` free for every `m ≥ 1`, the index of `L_j` for every prime;
- the basis in the final theorem indexed by any finite type;
- in W2, Lemma C proved by mixed second differences instead of the paper's polynomial dictionary, with the same statement.

---

## 6. Data per piece

- **Tarball, md5:** the project returned by Aristotle, file `884019b5-…-aristotle (N).tar.gz` in `~/Downloads`, first 8 hex digits of its md5.
- **Downloaded:** local time the file was saved (CEST). This bounds the completion of the Aristotle task.
- **Build, peak memory:** the local `lake build` of the new file, measured by the watchdog: wall-clock seconds including `lake`'s start-up, and the largest resident memory it sampled.
- **Lines / theorems / definitions:** of the file, in the final project. Theorems are the lines starting with `theorem` or `lemma`; definitions those starting with `def`, `abbrev`, `structure`, `inductive`, `instance` or `class` (possibly after `noncomputable`, `private` or `protected`).
- **Checks:** the brute-force check made before sending, with its negative control.

| # | Aristotle task | Tarball | md5 | Downloaded | Build (s) | Peak (GB) | Lines | Thms | Defs | Checks before sending |
|---|---|---|---|---|---|---|---|---|---|---|
| W1 | `bfec8091` | (base) | `fe4ea007` | 29 Sep 21:54 | 178 | 2.33 | 188 + 293 | 15 + 21 | 17 + 1 | `m = 5, 7, 11`: `G` symmetric, `G·N_j = m·𝟙`, R.1; fibre formulas for `G·y`. `m = 5, 7` (Macaulay2): `m \| aug(x_j)` on `K`, rank `V = 37, 91`, product of the non-zero elementary divisors of `G` `= 5^{12}, 7^{48}`. Control: a partial fibre functional is not divisible by `m` on `K` |
| W2 | `f501afa3` | (1) | `c10d5251` | 29 Sep 22:21 | 53 | 2.12 | 554 | 32 | 23 | `m = 3, 5, 7, 11`: the translation `x ↦ x − 1` in the term shared by families 1 and 3 is the only one with `SAT ⊆ K`; controls (other shifts, swapped pencils) fail. `m = 5, 7, 11`: `rank_Q = 9m − 7`, rank mod `m` `= 9m − 19`, kernel `12`. Relations of dimension `12` at `m = 5, 7, 11, 13`; `m = 3` gives `11` (control) |
| W3 | `d004cb9e` | (2) | `8a6ed828` | 29 Sep 22:45 | 47 | 2.08 | 467 | 33 | 1 | `m = 3, 4, 5, 6, 7, 9, 11, 15`: a basis and 20 random admissible data lie in `K`; `rank_Q = 9m − 7` for odd `m`. Control: a datum without sum zero is not in `K` |
| W4 | `b499b938` | (3) | `f1aa3d2c` | 29 Sep 23:09 | 51 | 2.17 | 355 | 25 | 5 | overlap formulas, diagnosed at `m = 5` (see §5), re-checked at `m = 5, 7, 11` on a basis of `Z₀`, control fails; `[Z^{m²} : L_j] = 5^{16}, 7^{29}, 11^{67}`; `\|det\|` of the Gram of `F` `= 5^{84}, 7^{198}` |
| W5 | `2aa54b1f` | (5) | `c9168c9c` | 29 Sep 23:37 | 76 | 1.64 | 413 | 30 | 6 | `m = 5, 7`: census and `m·x = satMap(D)` with `D` admissible, exact on all 38 and 56 vectors of a basis of `ker G` (Macaulay2) |
| W6 | `cdf7f149` | (6) | `1eb51b50` | 30 Sep 00:08 | 64 | 1.81 | 802 | 61 | 18 | `m = 5, 7`: `F` and `SAT` together have `3m²` generators and `[A : F + SAT] = 5^{48}, 7^{87}` exactly; `m = 5` (Macaulay2): `[A : F + K] = 5^{36}`, `[K : SAT] = 5^{12}`; `m = 7`: `[A : F + K] = 7^{75}` |
| W7 | `c097cb76` | (7) | `c0b960aa` | 30 Sep 07:04 | 89 | 1.37 | 249 | 15 | 5 | `m = 5, 7`: `det` of the Gram of `F` `= +5^{84}, +7^{198}` (sign checked); hence `det Gram_b = 5^{12}, 7^{48}` |

**Notes on the table.**
- The build of W1 compiled `Main.lean` (161 s), `Defs.lean` and `W1.lean` (60 s) together. Its lines, theorems and definitions are given as `Defs + W1`.
- Tarball `(4)` (md5 `c098ed1c`, 29 Sep 23:24) is the premature download of §5, not used.
- At `m = 7` the Macaulay2 computation of `[K : SAT]` was stopped by the watchdog at 1.2 GB. It is not needed: `[K : SAT] = m^{12}` is a Lean theorem.
- The builds are incremental: each builds only the new file on top of the compiled project. The clean rebuild of everything is in §8.
- The check runs (`#check` and `#print axioms`) took 92–139 s each, peak 1.59–2.52 GB (logs `check_run*.log`).

---

## 7. Totals

| Quantity | Value |
|---|---|
| Pieces sent to Aristotle | 7 (one task each) |
| Properties registered by Aristotle | 31 PROVED, 0 NEGATED, 0 in progress |
| Lean files | 9 (`Defs`, `W1`–`W7`, and the unused header `Main.lean`) |
| Lines of Lean | 3 345 |
| Theorems and lemmas (`theorem`/`lemma` at the start of a line) | 232 |
| Definitions (`def`, `abbrev`, `structure`, `inductive`, `instance`, `class`) | 76 |
| `sorry` / `admit` / added axioms / `native_decide` / `decide` | 0 / 0 / 0 / 0 / 0 |
| Axioms of `watermark_theorem` | `propext`, `Classical.choice`, `Quot.sound` |
| Calendar time | first result downloaded 29 Sep 21:54, last 30 Sep 07:04; work paused during the night between W7 being sent and its download |
| Sum of the 7 incremental local builds | 558 s = 9.3 min |
| Largest local build | 178 s (W1, with the project header); peak memory 2.33 GB (W1) |
| Clean rebuild of the whole project, one module at a time | 9 of 9 modules, all exit 0; 07:43:16 → 07:54:21 on 30 Sep, i.e. 11 min 05 s wall-clock (658 s inside the 9 `lake build` calls); slowest module `Main.lean`, 168 s, and among the Watermark files `W7`, 89 s; peak memory 2.16 GB (`Defs`) |
| Declarations of the project in the dependency cone of `watermark_theorem` | 410, in 8 files (§3.2) |

---

## 8. Reproducibility

**Machine:** Apple Mac (arm64), 8 CPU cores, 8 GB of memory, macOS (Darwin 25.5.0).

**Toolchain:** `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` = commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (from `lake-manifest.json`). These are the same toolchain and the same Mathlib as the Lean certificate of *The Chaise Longue Theorem*.

**Commands**, from the project root:

```
lake exe cache get                # Mathlib's compiled files
lake build                        # all 9 files; exit 0
lake env lean checks/CheckFinal.lean
                                  # #check, #print of the definitions, #print axioms,
                                  # and the non-vacuity example at m = 5
```

**Clean rebuild.** On 30 Sep 2026 the project's own build directory was moved aside (Mathlib untouched) and the 9 modules were rebuilt one at a time in dependency order, each with its own `lake build` inside the watchdog, so that only one Lean process ran at once. All 9 built with exit code 0, from 07:43:16 to 07:54:21 (11 min 05 s), with 658 s spent inside the 9 `lake build` calls: `Main` 168 s, `Defs` 40 s, `W1` 62 s, `W2` 69 s, `W3` 55 s, `W4` 63 s, `W5` 45 s, `W6` 67 s, `W7` 89 s. Afterwards a plain `lake build` reported «Build completed successfully (8035 jobs)». On the fresh build, `checks/CheckFinal.lean` printed exactly the same output as before, including the axioms `[propext, Classical.choice, Quot.sound]`, and the non-vacuity example compiled again. Logs: `clean_rebuild_2026-09-30.log`, one `cr_<module>.log` per module, `cr_all.log`, `checkfinal_fresh.log`.

**Fingerprints of the source:**
- SHA-256 of the concatenation of the 9 `.lean` files, in sorted path order: `489fcfc254013cb8d40d41d84755887213218bb7f7a2760871850af4e6d53a0a`.
- SHA-256 of the list of their individual SHA-256 lines (`shasum -a 256 $(find RequestProject -name '*.lean' | sort) | shasum -a 256`): `1d331fbbf90a629ba79aee1a8d19120a9823bd77969affd6db7f740582cecf6e`.
- SHA-256 of each file:

| File | SHA-256 |
|---|---|
| `RequestProject/Main.lean` | `929b0bddef0b781f3fb42c7a99f252dc0bda7331f698104f7075e12ff637c52d` |
| `RequestProject/Watermark/Defs.lean` | `0af5ba018edd1a64138a40349e3d448062cdb20dbb5c2634198f47ff19af12b5` |
| `RequestProject/Watermark/W1.lean` | `fe5a814f4feba342697dd66dcaa9d95d403a06d4e458afc9014e08664649075a` |
| `RequestProject/Watermark/W2.lean` | `29580b50a72a8b11bf02c2f622198e632ff92b0df4386ebe4fd5dc46395c9342` |
| `RequestProject/Watermark/W3.lean` | `61a2e26993834c755c580c39dd01b0b936f5657eeef8f88c4c4208a9ffbefbd7` |
| `RequestProject/Watermark/W4.lean` | `a2419a27d3bf7d6c14e94135258f51271142b7049695ed379c84e78553077a06` |
| `RequestProject/Watermark/W5.lean` | `05a5311a1761f00fc1c260548d0d6f43a981384abe286a59f1ec3a2d42eb4858` |
| `RequestProject/Watermark/W6.lean` | `f0fbd352eee1f075ec7640643fe68b0eb8303ef4404be7a4155644309b734839` |
| `RequestProject/Watermark/W7.lean` | `bc93a6455c604248ebfa186150b7f6eb66662c0c65c4ad1738df8d499f473a58` |

**The project now holds 12 files.** After this certificate, the three files of the Double Ladder (`RequestProject/DoubleLadder/DL1.lean`, `DL2.lean`, `DL3.lean`) were added to the same project [DL-Lean]. The nine files above are unchanged: their SHA-256 values, and the SHA-256 of their concatenation, were checked again on 30 September after the Double Ladder was certified, and they are identical. The fingerprints of all 12 files are in [DL-Lean, §8].

**Where the files are published.** The repository `github.com/tretoef-estrella/watermark-theorem` holds the whole Lean folder as `lean/` (see its `README.md`). There, the Lean project `proyecto/` is `lean/project/`, and everything else listed below is in `lean/watermark/`, with the same names and the same relative paths. The returned projects `run1/ … run7/` are not published: each is a full copy of the project at that stage, and the final files are in `project/`. The Macaulay2 outputs `checks/kerG5.txt` and `checks/kerG7.txt` (118 MB) are not published either; `checks/kerexp5.m2` and `checks/kerexp7.m2` regenerate them. From the root of `project/`, the check of §8 is `lake env lean ../watermark/checks/CheckFinal.lean`.

**On the author's machine** (folder `ARISTOTLE_LEAN/WATERMARK/` of the author's archive):
- `proyecto/`: the Lean project;
- `run1/ … run7/`: every returned project, extracted;
- `pieces/`: the seven pieces sent;
- `checks/`: the brute-force scripts and their logs, the Lean check files `Check1.lean` … `Check7.lean`, `CheckFinal.lean`, `DepsFinal.lean`, and the geometry check `wfinal_geometry.py`;
- `build_run1.log` … `build_run7.log`, `check_run1.log` … `check_run7.log`: every build and every check, for all seven runs;
- `checkfinal.log`, `checkfinal_fresh.log`, `deps_watermark.log`, `clean_rebuild_2026-09-30.log` and the per-module logs `cr_*.log`;
- `ESTADO_WATERMARK.md`: the state file, one section per run.

**Recommended to a reader who wants to remove the remaining trust in the author's logs:** an independent `lake build` on another machine, and a run of `lean4checker` on the compiled project. Neither has been done yet.

---

## 9. What this certificate claims, in one paragraph

A computer proof assistant, Lean 4 with the Mathlib library, has checked a complete proof of the following statement, with no gap and no axiom beyond the three standard ones:

> For every prime `m ≥ 5`, let `G` be the explicit `3m² × 3m²` integer matrix of §1.2 and `V = Z^{3m²}/ker G` with the form induced by `G`. Then `V` is a free abelian group of rank `3(m−1)(m−2)+1`, and the Gram determinant of every `Z`-basis of `V` equals `m^{3(m−3)²}`.

`G` is the intersection matrix of the `3m²` lines on the Fermat surface `S_m` (§1.4: proved by hand, checked by computer, not formalized). So `V` is the lattice of the lines, and by [SSvL] and [Deg] it is `NS(S_m)` for prime `m`. The statement is therefore the formula `disc NS(S_m) = m^{3(m−3)²}`, asked for by Shioda in 1987 (Questions 7.2 and 7.4), for every prime `m ≥ 5`.

The proofs in Lean were written by the AI system Aristotle (Harmonic) from pieces written by the author. The author's audit, assisted by Claude (Anthropic), checked that the statements match the paper, and compiled and re-checked everything on his own machine.

## 10. What was known before

This section records what we found in the literature on 30 September 2026. A search cannot prove that nothing exists; it records what we looked at. Every source below was read in the original.

- **Shioda (1987)** [Sh87], §7, p. 133. *Question 7.2*: for the Fermat surface of prime degree `m` in characteristic `p ≡ 1 (mod m)`, is `|det NS(X)| = m^{3(m−3)²}`? *Question 7.4 (i)*: for the complex Fermat surface of prime degree `m`, are (7.10) `|det NS| = m^{3(m−3)²}` and (7.11) «`NS` is spanned by the classes of lines» true? He asks for the determinant only. «Added in proof» (1): the discriminant divides a power of `m` for every `m`. For every prime `m ≥ 5`, the Watermark Theorem answers (7.10) for the lattice of the lines, and [Deg] answers (7.11); together they give (7.10) for `NS`.
- **Schütt, Shioda, van Luijk (2010)** [SSvL], arXiv source. End of §4: for every odd `m ≤ 81`, the determinant of the intersection form on their basis of lines is `m^{3(m−3)²}`, «with exponent as conjectured in [Sh87]». They prove that the lines span `NS ⊗ Q`, and span `NS` for `m ≤ 100` with `gcd(m, 6) = 1`.
- **Degtyarev (2015)** [Deg], arXiv source. For every `m ≤ 4` and every `m` with `gcd(m, 6) = 1`, the lines generate `NS(S_m)` over `Z`. The proof is topological; it gives no discriminant.
- **Shioda (2015)** [Sh15], §6.5, Conjecture 23: for `m` prime to `6`, `det NS(X_m) = m^{3(m−3)²}` appears inside a conjecture on Mordell–Weil lattices. In 2015 the formula was still used as expected, not as proved.
- **Aljovin, Movasati, Villaflor (2019)** [AMV], Table 1: the elementary divisors of the lattice of linear cycles of the Fermat surface, computed by machine (Smith normal form, one cell at a time) for `3 ≤ m ≤ 14`. For prime `m` the rows are `(2,5)`: `1^{26} · 5^{10} · 25`; `(2,7)`: `1^{48} · 7^{38} · 49^{5}`; `(2,11)`: `1^{96} · 11^{158} · 121^{17}`; `(2,13)`: `1^{120} · 13^{254} · 169^{23}`. The products are `5^{12}`, `7^{48}`, `11^{192}` and `13^{300}`, which are `m^{3(m−3)²}` in each case. [AMV] give no general formula and no proof for general `m`.

**Therefore.** Before June 2026 the formula `m^{3(m−3)²}` was asked for by Shioda for prime `m`, checked by computer for every odd `m ≤ 81`, and read off by computer from the elementary divisors for `m ≤ 14`. As far as we could determine, its proof for every prime `m ≥ 5` is new; it is now certified in Lean. The structure of the group, which goes beyond Shioda's question, is the Double Ladder Theorem [DL-Lean].

## References

- [AMV] E. Aljovin, H. Movasati, R. Villaflor, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184; arXiv:1711.02628.
- [CL-Lean] R. Amichis Luengo, *The Chaise Longue Theorem — Lean Certificate*, v1, Zenodo 2026, DOI 10.5281/zenodo.23045371.
- [DL-Lean] R. Amichis Luengo, *The Double Ladder Theorem — Lean Certificate*, 30 September 2026; repository `github.com/tretoef-estrella/watermark-theorem`, folder `lean/double-ladder/`.
- [Deg] A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477; doi:10.1016/j.jnt.2014.07.020; arXiv:1305.3073.
- [Sh87] T. Shioda, *Some observations on Jacobi sums*, in: Galois Representations and Arithmetic Algebraic Geometry (Kyoto 1985 / Tokyo 1986), Adv. Stud. Pure Math. **12** (1987), 119–135; doi:10.2969/aspm/01210119.
- [Sh15] T. Shioda, *Mordell–Weil lattice of higher genus fibration on a Fermat surface*, J. Math. Sci. Univ. Tokyo **22** (2015), 443–468.
- [SSvL] M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), no. 9, 1939–1963; doi:10.1016/j.jnt.2010.01.008; arXiv:0812.2377.
- R. Amichis Luengo, *The Watermark Theorem*, v1.0, 4 June 2026, repository `github.com/tretoef-estrella/chaise-longue-theorem`, `hodge-fermat-campaign/THE_WATERMARK_THEOREM.md`.
- The Lean 4 theorem prover, https://lean-lang.org; the Mathlib library, https://github.com/leanprover-community/mathlib4.
- Aristotle, Harmonic, https://aristotle.harmonic.fun.

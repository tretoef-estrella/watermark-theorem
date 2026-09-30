# The Double Ladder Theorem — a pencil proof

**Rafael Amichis Luengo** · Madrid · written with Claude (Anthropic) · version 2, 30 September 2026

*Version 2 is the text of version 1 (the same day) after a cold read by an independent reader, who found no mathematical gap. It updates the status, states two steps more fully (the linear independence in Lemma 3.1 and the passage from the Smith form to `V*/V` in §4), corrects the novelty claims of §5–§6, and says how the Lean proof differs in its details.*

## 0. Statement and status

Let `m ≥ 5` be prime. Let `G` be the integer Gram matrix of the `3m²` lines on the Fermat surface of degree `m` (the matrix `Watermark.gram m` of the Lean project), let `K = ker G`, `V = ℤ^{3m²}/K`, and give `V` the form induced by `G`.

> **Theorem (Double Ladder).** `V*/V ≅ (ℤ/m)^{3m²−24m+59} × (ℤ/m²)^{3m−16}` for every prime `m ≥ 7`. For `m = 5` it is `(ℤ/5)^{10} × ℤ/25`.

The statement is that of *The Double Ladder Theorem* (5 June 2026). That paper proves it by a character route in which four steps, in its §4 and §6, were confirmed at three or four primes and not written for general `m` (its version note of 30 September 2026 lists them). The proof below is different, short, and uses only integer lattice facts already certified in Lean for the Watermark (W1–W7). It rests on three facts:

1. **Order** (the Watermark Theorem, certified in Lean): `|V*/V| = m^{3(m−3)²}`.
2. **Exponent** (§2): `m² · V* ⊆ V`, from an explicit identity `G Y G = 6m² G`.
3. **Rank mod m** (§3): `rank_{𝔽_m}(G mod m) = 12(m − 3)` for `m ≥ 7`, and `26` for `m = 5`.

**Status.** All three facts and the assembly are certified in Lean 4 with Mathlib (30 September 2026): Fact 1 is the Watermark (W1–W7), Fact 2 is piece DL1, Fact 3 is DL2, and the assembly is DL3. The final theorems depend only on the standard axioms. The Lean certificate describes each piece and the few places where the Lean proof takes a different path from the text below (§7).

## 1. Notation

- `Ω = (ℤ/m)²`. A line is `(j, k, l)`, `j ∈ {0, 1, 2}`, `(k, l) ∈ Ω`.
- The four pencils used below are the linear forms `k`, `l`, `k − l`, `k + l` on `Ω`. They are pairwise independent because `m` is odd.
- `P_π(p, q) = 1` if the pencil `π` takes the same value at `p` and `q` (same family), else `0`.
- The rows of `G` are those of the Watermark:
  - self-intersection `2 − m`;
  - `1` for two lines of one family sharing `k` or `l`;
  - `1` across families on one incidence set, of the form `{k′ − l′ = c}` or `{k′ + l′ = c}`: family 0 meets family 1 on `k − l`, family 1 meets family 2 on `k + l`, family 0 meets family 2 on (`k + l` of family 0) = (`k − l` of family 2) − 1.

## 2. The exponent: `G Y G = 6m² G`

Define `Y` block-diagonally, family by family:

`Y = P_k + P_l + 3 P_{k−l} + 3 P_{k+l} − 6m · I`.

**Lemma 2.1.** `G Y G = 6m² G`.

*Proof.* By W4, `ℚ^{3m²}` is spanned by two kinds of vectors:
- the pullbacks `pb_j^π(u)` along the `m + 1` pencils `π` of each family, with `u` of sum zero;
- the three family vectors `N_j`.

(W4.c gives `m · e_{(j,p)}` as such a combination.) So it suffices to check the identity on these vectors.

*`Y` on these vectors.* On one family, `P_π pb^{π′}(u) = m·pb^{π}(u)` if `π′ = π` (each fibre has `m` points), and `= 0` if `π′ ≠ π` (each fibre of `π` meets each fibre of `π′` in one point, and `Σu = 0`). Also `P_π N_j = m N_j`. Hence `Y` acts:
- on axis pullbacks (`k`, `l`) by `−5m`;
- on overlap pullbacks (`k ± l`) by `−3m`;
- on the other live pullbacks by `−6m`;
- on `N_j` by `+2m`.

*`G` on the same vectors* (W4.b, W1.b):
- axis pullbacks: `0`;
- live pullbacks: `−m`;
- overlap pullbacks come in pairs `v, v′` with `Gv = −m v + m v′` and `Gv′ = −m v′ + m v` (one pair carries a shift by one, which cancels);
- `G N_j = m 𝟙` and `G 𝟙 = 3m 𝟙`.

*Check.*
- Axis: both sides are `0`.
- Live: `(−m)(−6m)(−m) = −6m³ = 6m²(−m)`.
- Overlap: `G = mB` with `B = [[−1, 1], [1, −1]]` and `B² = −2B`, so `mB·(−3m)·mB = −3m³B² = 6m³B = 6m²·G`.
- Family vectors: on `span(N_j)`, `G = mJ₃`, `J₃² = 3J₃` and `Y = 2m`, so `mJ·2m·mJ = 6m³J = 6m²·G`. ∎

*Meaning.* `G` has minimal polynomial `x(x + m)(x + 2m)(x − 3m)`, and `Y` acts as `6m²/λ` on the `λ`-eigenspace for every `λ ≠ 0`. The integer `6` is forced: it is the least common denominator of `m²/λ` over `λ/m ∈ {−1, −2, 3}`. It is the same `6` as the "autograph determinant" of the June document, and there as here it is harmless because `gcd(6, m) = 1`.

**Corollary 2.2.** `m² · V* ⊆ V`, i.e. the exponent of `V*/V` divides `m²`.

*Proof.* A functional on `V` is a vector `f ∈ ℤ^{3m²}` orthogonal to `K`, hence `f = G y` with `y ∈ ℚ^{3m²}`. By Lemma 2.1, `6m² f = G Y G y = G(Y f)`, the class of the integer vector `Y f`. So `6m² V* ⊆ V`. `V*/V` has order `m^{3(m−3)²}` (Fact 1), a power of the prime `m ≥ 5`, so `6` acts invertibly on it and `m² V* ⊆ V`. ∎

## 3. The rank of `G` modulo `m`

Over `𝔽_m` we have `G ≡ M := G + mI`, the 0/1 incidence matrix with `2` on the diagonal.

**The shadow factorization.** For each family `j` and each of its four pencils `π ∈ {k, l, k − l, k + l}`, let `push_{j,π} : 𝔽_m^{Ω} → 𝔽_m^{ℤ/m}` sum over the fibres of `π`. This gives twelve shadows: `S : 𝔽_m^{3m²} → U := (𝔽_m^{ℤ/m})^{12}`. Let `Γ` be the symmetric matrix on `U` that:
- pairs each axis slot `(j, k)`, `(j, l)` with itself by the identity;
- pairs the cross slots `(0, k − l) ↔ (1, k − l)` and `(1, k + l) ↔ (2, k + l)` by the identity;
- pairs `(0, k + l) ↔ (2, k − l)` by the shift `x ↦ x + 1`.

Then **`G = Sᵀ Γ S − m I` over `ℤ`** (checked entry by entry). So `G mod m = Sᵀ Γ S`, and

`rank(G mod m) = dim W − dim(W ∩ W^{⊥Γ})`, where `W = im S`.

**Lemma 3.1.** `dim W = 12m − 18`, and the annihilator of `W` is the 18-dimensional space `R` spanned, family by family, by the relations
`Σ_π c_π · x^s` placed in the four slots, `s ∈ {0, 1, 2}`, with `Σ_π c_π π^s ≡ 0` as a form on `Ω`.
These are `3 + 2 + 1 = 6` relations per family: three constants, two linear, and the polarization identity `(k + l)² + (k − l)² = 2k² + 2l²`.

*Proof.* `(h_π)` annihilates `W_j` iff `Σ_π h_π(π(k, l)) = 0` as a function on `Ω`. Write `h_π` as a polynomial of degree `≤ m − 1`. The left side is then a polynomial of total degree `≤ m − 1`, so it vanishes as a function iff it vanishes as a polynomial, iff each homogeneous part vanishes: `Σ_π c_{π,s} π^s = 0` for every `s`.

The four powers `π^s` of pairwise independent linear forms are linearly independent once `3 ≤ s < m`. Indeed, write `π = a k + b l`. The coefficient of `k^t l^{s−t}` in `π^s` is `C(s, t) a^t b^{s−t}`, and every `C(s, t)` with `0 ≤ t ≤ s < m` is a unit mod `m`. So the coefficient matrix of the four powers is a Vandermonde-type matrix in the four distinct points `(a : b)` of `P¹(𝔽_m)`, multiplied by an invertible diagonal matrix; it has rank `4`. (At `s = 3` the relevant minor is `−18`, a unit because `m ≥ 5`.) They span a space of dimension `s + 1` for `s ≤ 2` (`char ≠ 2`). So the relations live in degrees `0, 1, 2`, with `3, 2, 1` of them. ∎

**Lemma 3.2.** For `m ≥ 7`, `W^{⊥Γ} ⊆ W`; hence `dim(W ∩ W^{⊥Γ}) = 18`.

*Proof.* `W^{⊥Γ} = Γ⁻¹ R = Γ R` (`Γ² = I`). The entries of a vector of `Γ R` are polynomials of degree `≤ 2` in the slot variable, possibly composed with `x ↦ x ± 1`. A vector lies in `W` iff it is orthogonal to `R`, and each such pairing is `Σ_{x ∈ 𝔽_m} p(x) q(x)` with `deg(pq) ≤ 4`. Since `Σ_{x ∈ 𝔽_m} x^s = 0` for `0 ≤ s ≤ m − 2`, and `4 ≤ m − 3` when `m ≥ 7`, every pairing vanishes. ∎

**Corollary 3.3.** `rank_{𝔽_m}(G mod m) = (12m − 18) − 18 = 12(m − 3)` for every prime `m ≥ 7`.

**The case `m = 5`.** Here `Σ_{x ∈ 𝔽_5} x⁴ = −1 ≠ 0`, so the degree-4 pairings survive. The `18 × 18` matrix of `Γ`-pairings between relations has rank `2`, giving `dim(W ∩ W^{⊥Γ}) = 16` and rank `26` (measured). This is exactly the "`+2` at `m = 5`" of the June document, now with its cause: `4 = m − 1`.

## 4. Assembly

Since `K` is saturated (W5), `ℤ^{3m²} = K ⊕ C` for a complement `C ≅ V`, and in a basis adapted to this splitting `G` is `0 ⊕ Gram(V)`. So the non-zero elementary divisors of `G` are those of `Gram(V)`, whose cokernel is `V*/V`. Put `G` in local Smith form over `ℤ_{(m)}`. Its elementary divisors are:
- `n₀` of valuation 0, `n₁` of valuation 1, `n₂` of valuation 2;
- none of valuation `≥ 3` (Corollary 2.2);
- `9m − 7` zeros (the kernel `K`, saturated, of rank `9m − 7`: W5).

Then `V*/V ≅ (ℤ/m)^{n₁} × (ℤ/m²)^{n₂}`, `n₀ + n₁ + n₂ = rank V = 3(m−1)(m−2)+1`, and:
- `n₀ = rank(G mod m) = 12(m − 3)` (Corollary 3.3), so `n₁ + n₂ = 3m² − 21m + 43`;
- `n₁ + 2n₂ = 3(m − 3)²` (Fact 1).

Subtracting, **`n₂ = 3m − 16`** and **`n₁ = 3m² − 24m + 59`**. For `m = 5`: `n₀ = 26`, `n₁ + n₂ = 11`, `n₁ + 2n₂ = 12`, so `n₂ = 1` and `n₁ = 10`. ∎

## 5. Checks (all run 30 Sep; scripts in `DOUBLE_LADDER/checks/`)

| check | m = 5 | 7 | 11 | 13 | 17 |
|---|---|---|---|---|---|
| `G Y G = 6m² G` (exact) | ✓ | ✓ | ✓ | ✓ | ✓ |
| control `G Y G = 6m G` | fails | fails | fails | fails | fails |
| minimal polynomial `x(x+m)(x+2m)(x−3m)` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `G = SᵀΓS − mI` | ✓ | ✓ | ✓ | ✓ | |
| `dim W_j = 4m − 6` | 14 | 22 | 38 | 46 | |
| `dim(W ∩ W^⊥)` | 16 | 18 | 18 | 18 | |
| `rank(G mod m)` | 26 | 48 | 96 | 120 | |
| Smith profile `{0: n₀, 1: n₁, 2: n₂}` | `{26, 10, 1}` | `{48, 38, 5}` | `{96, 158, 17}` | `{120, 254, 23}` | |

- The profiles at `m = 5, 7, 11, 13` agree with the rows `(2,5)`, `(2,7)`, `(2,11)`, `(2,13)` of Table 1 of Aljovin–Movasati–Villaflor (J. Symbolic Comput. 95 (2019); arXiv:1711.02628).

- In every case the number of divisors of valuation `≥ 4` (computed modulo `m⁴`) is exactly `9m − 7`: these are the zeros, the kernel `K`.
- Also checked: `Y` acts by `−5m / −3m / −6m / +2m` on the four kinds of vectors, family by family, at `m = 5, 7, 11, 13`.
- Scripts: `dl_profile.py`, `dl_eig.py`, `dl_wl.py` (the coherent closure of the configuration has 27 classes; `Y` was found inside it), `dl_sym.py` (the symmetric solutions of `G X G = m² G`: always denominator 6), `dl_cert.py`, `dl_steps.py`.

## 6. What is new, and what is not

- **Not new:** the statement (June 2026), and the values at `m = 5, 7, 11, 13`, which are in Table 1 of Aljovin–Movasati–Villaflor.
- **New:**
  - a proof in which every step is written for general `m`;
  - the reason for the `m = 5` exception (`Σx⁴ ≠ 0` in `𝔽_5`);
  - the certificate `Y` with its `6`.

- **Relation to the June proof:** Corollary 3.3 is rung `K = 0` of its rank ladder, proved directly. The certificate replaces its flat law, glue law and cap for the exponent.

## 7. How the Lean proof differs in its details

The Lean proof (DL1–DL3, 30 September 2026) proves the same three facts and the same assembly. Three details differ:
- **Lemma 2.1.** Lean checks `G Y G = 6m² G` on the same vectors. On an overlap pair `v, v′`, `G` mixes the two vectors, as displayed above, and Lean treats the pair jointly (`defect_pair`).
- **Lemma 3.1.** Lean identifies the relations by mixed second differences of functions on `ℤ/m`, not by writing functions as polynomials. The statement is the same.
- **§4.** Lean does not take a Smith form. It counts `|V*/V| = m^{3(m−3)²}` and `|(V*/V)/m(V*/V)| = m^{rank V − 12(m−3)}`, and a finite abelian `m`-group of exponent `m²` is determined by these two numbers (`equiv_of_card`).


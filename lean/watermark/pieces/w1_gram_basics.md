# The Watermark Theorem, piece W1: the line configuration, its Gram matrix, and the first identities

This is the first piece of a Lean 4 formalization of *The Watermark Theorem* (R. Amichis Luengo, 2026). The final target, for later pieces, is:

> **Theorem.** For every prime `m ≥ 5`, the lattice `V := A / ker G` defined below, with the bilinear form induced by `G`, has `|disc V| = m^{3(m−3)^2}`.

This piece only fixes the definitions, which every later piece will reuse unchanged, and proves the elementary identities below. Please choose definitions that later pieces can build on (a `Matrix` indexed by a `Fintype`, the kernel as a `Submodule ℤ`, the quotient as a `ℤ`-module).

## Setting

Let `m` be a natural number with `m ≥ 5` (and, where stated, `m` prime). Put `P := ZMod m × ZMod m`, the set of **points** `(k, l)`, and `I := Fin 3 × P`, the set of **lines** `(j, k, l)`. Here `j = 0, 1, 2` stands for the families 1, 2, 3 of the paper. `|I| = 3m²`.

The **Gram matrix** `G : Matrix I I ℤ` is defined as follows, for `p = (j, k, l)` and `p′ = (j′, k′, l′)`.

- **Same family** (`j = j′`): `G p p = 2 − m`; for `(k, l) ≠ (k′, l′)`, `G p p′ = 1` if `k = k′` or `l = l′`, and `0` otherwise.
- **Families 0 and 1** (`j = 0`, `j′ = 1`): `G p p′ = 1` iff `k − l = k′ − l′`, else `0`.
- **Families 1 and 2** (`j = 1`, `j′ = 2`): `G p p′ = 1` iff `k + l = k′ + l′`, else `0`.
- **Families 0 and 2** (`j = 0`, `j′ = 2`): `G p p′ = 1` iff `k′ − l′ = k + l + 1`, else `0`.
- The remaining cases, `j > j′`, are defined by symmetry: `G p p′ := G p′ p`.

All equalities of coordinates are in `ZMod m`.

Let `A := I → ℤ`, and let `G` act on `A` by `(G x)(p) = Σ_{p′} G p p′ · x(p′)`. Put `K := ker G` (a `ℤ`-submodule of `A`) and **`V := A ⧸ K`**. The form `B(x, y) := Σ_{p,p′} x(p) · G p p′ · y(p′)` on `A` vanishes when either argument lies in `K`, so it induces a symmetric bilinear form on `V`. Please define this induced form too; it is needed for the final discriminant.

For `j ∈ Fin 3`, let `N_j ∈ A` be the indicator of family `j` (`N_j(j′, k, l) = 1` if `j′ = j`, else `0`). For `x ∈ A`, write `x_j` for its restriction to family `j` (a function `P → ℤ`), and put `aug(x_j) := Σ_{(k,l) ∈ P} x(j, k, l)`.

**Pencils.** For `t ∈ ZMod m`, put `π_t(k, l) := k + t·l`, and put `π_∞(k, l) := l`. These are the `m + 1` pencils. For a pencil `π` and `u : P → ℤ`, put `(E_π u)(p) := Σ_{p′ ∈ P, π(p′) = π(p)} u(p′)`.

## Statements

**(W1.a) Symmetry.** `G` is symmetric: `Gᵀ = G`.

**(W1.b) The family vectors.** For every `j`, `G · N_j = m · 𝟙`, where `𝟙 ∈ A` is the all-ones vector.

**(W1.c) The incidence identity (paper, Lemma R.1).** For every `u : P → ℤ` and every `p ∈ P`, with `m` prime,

`Σ_{π ∈ {π_t : t ∈ ZMod m} ∪ {π_∞}} (E_π u)(p) = m · u(p) + Σ_{p′ ∈ P} u(p′)`.

**(W1.d) Augmentation divisibility (paper, Lemma R.2).** Let `m ≥ 5` be prime. For every `x ∈ K`:

- `aug(x_0) + aug(x_1) + aug(x_2) = 0`;
- `m ∣ aug(x_j)` for every `j`.

## Proofs

**(W1.a)** Immediate from the definition: the cases `j = j′` are symmetric in `(k, l) ↔ (k′, l′)`, and the cases `j ≠ j′` are defined by symmetry.

**(W1.b)** Fix a line `p = (j₀, k, l)`. If `j₀ = j`: the diagonal contributes `2 − m`; the points `(k, l′)` with `l′ ≠ l` contribute `m − 1`; the points `(k′, l)` with `k′ ≠ k` contribute `m − 1`. Total `2 − m + 2(m − 1) = m`. If `j₀ ≠ j`: each cross-family incidence condition is one linear equation in `(k′, l′)`, of the form `k′ − l′ = c` or `k′ + l′ = c`. It has exactly `m` solutions in `P`. Total `m`.

**(W1.c)** Fix `p ≠ p′` in `P`. The difference `p′ − p ≠ 0` lies on exactly one of the `m + 1` lines through `0` in `(ZMod m)²` (here `m` prime is used). So exactly one pencil takes the same value at `p` and `p′`, and the coefficient of `u(p′)` on the left is `1`. The coefficient of `u(p)` is `m + 1` (every pencil takes the same value at `p` and `p`). This gives `m · u(p) + Σ_{p′} u(p′)`.

**(W1.d)** *The sum.* By (W1.a) and (W1.b), `B(N_j, x) = (G N_j) · x = m · Σ_{p} x(p)`. For `x ∈ K`, `B(N_j, x) = N_j · (G x) = 0`, so `Σ_p x(p) = 0`; this is `aug(x_0) + aug(x_1) + aug(x_2) = 0`.

*Divisibility.* Pair `x` with the indicator `y` of a fibre of a live pencil of family 0, `y := 𝟙{(0, k, l) : k + t·l = c}` with `t ≠ 0`. Then `0 = (G y) · x`. The paper computes `G y` explicitly (Lemma R.2). Within family 0, `(G y)|_0 = 2 · 𝟙_0 − m · y`. The fibre is a graph over `k` and over `l`, so each point off the fibre sees exactly two fibre points, one in its row and one in its column; each point on the fibre sees itself (`2 − m`) and no other fibre point in its row or column. Across families the incidence condition, restricted to the fibre, is a bijection, except for one exceptional slope in the block (0,1) (`t = −1`) and one in the block (0,2) (`t = 1`). This gives:

- `G y = 2·𝟙_0 + 𝟙_1 + 𝟙_2 − m·y` for `t ∉ {0, 1, −1}`;
- `G y = 2·𝟙_0 + 𝟙_1 + m·z_2 − m·y` at `t = 1`;
- `G y = 2·𝟙_0 + m·z_1 + 𝟙_2 − m·y` at `t = −1`.

Here `z_1`, `z_2` are indicators of one fibre in the exceptional family. (Any valid computation of `G y` may be used instead; only the reductions mod `m` below matter.) Pairing with `x ∈ K` and reducing mod `m`, with `a_j := aug(x_j)`, gives `2a_0 + a_1 + a_2 ≡ 0`, `2a_0 + a_1 ≡ 0` and `2a_0 + a_2 ≡ 0 (mod m)`. A slope `t ∉ {0, 1, −1}` exists because `m ≥ 5`. Subtracting, `a_1 ≡ a_2 ≡ 0` and `2a_0 ≡ 0`, hence `a_0 ≡ 0` since `m` is odd.

## Checks (run before sending)

- `m = 5, 7, 11`: (W1.a), (W1.b) and (W1.c) hold for every entry (the matrices have 75, 147 and 363 rows).
- `m = 5, 7`, in Macaulay2, with `K` the kernel of `G` over `ℤ`:
  - `rank K = 38, 56` (`= 9m − 7`);
  - `aug(x_0) + aug(x_1) + aug(x_2) = 0` and `m ∣ aug(x_j)` for every basis vector of `K`.
- **Negative control:** the functional «sum over the points of family 0 with `l < 2`» is **not** divisible by `m` on `K`, at both primes.
- **Sanity check of the final target**, not part of this piece: the non-zero elementary divisors of `G` have product `5^12` at `m = 5` and `7^48` at `m = 7`. These equal `m^{3(m−3)^2}` and are `|disc V|`. `rank V = 37, 91` (`= 3(m−1)(m−2) + 1`).

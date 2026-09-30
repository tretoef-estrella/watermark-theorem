# The Watermark Theorem, piece W3: SAT lies in the kernel of G, and satMap is injective over ℤ

Third piece of the Lean 4 formalization of *The Watermark Theorem*. Pieces W1 and W2 are already in this project (`RequestProject/Watermark/Defs.lean`, `W1.lean`, `W2.lean`, namespace `Watermark`). **Reuse their definitions unchanged and do not edit those files.** Put this piece in `RequestProject/Watermark/W3.lean`.

The paper (§7) states `SAT ⊂ K` and `rank SAT = 9m − 7` as «file-verified»; this piece proves them.

## Setting (from W1 and W2)

`gram m` is the Gram matrix `G`, `K m = ker G ⊆ A m = (Line m → ℤ)`; `satMap R m`, `SatSrc R m` and `SAT m = satMap ℤ m (SatSrc ℤ m)` are as in W2:

- family 0: `a_0(k) + b_0(l) + w_0(k − l) + w_2(k + l) + ε₁`;
- family 1: `a_1(k) + b_1(l) + w_0(k − l) + w_1(k + l) + (ε₂ − ε₁)`;
- family 2: `a_2(k) + b_2(l) + w_1(k + l) + w_2(k − l − 1) − ε₂`,

with the nine functions `a_j, b_j, w_i : ZMod m → ℤ` sum-zero.

## Statements

**(W3.a) SAT ⊂ K.** For every `m ≥ 1` (`[NeZero m]`) and every `D ∈ SatSrc ℤ m`: `gram m *ᵥ satMap ℤ m D = 0`. Hence `SAT m ≤ K m`.

**(W3.b) Injectivity.** For every odd `m ≥ 3`, `satMap ℤ m` is injective on `SatSrc ℤ m`: if `D ∈ SatSrc ℤ m` and `satMap ℤ m D = 0`, then `D = 0`.

**(W3.c) Rank.** For every odd `m ≥ 3`, `Module.finrank ℤ (SAT m) = 9m − 7`.

## Proofs

**The row of G.** For a line `p = (j, k, l)`, the row of `G` has: `2 − m` at `p`; `1` at the lines `(j, k, l′)`, `l′ ≠ l`, and `(j, k′, l)`, `k′ ≠ k`; and, in each other family `j′`, `1` exactly on an *incidence set* `S_{j′}(p) ⊆ P`:

- `p` in family 0, `j′ = 1`: `k′ − l′ = k − l`; `j′ = 2`: `k′ − l′ = k + l + 1`;
- `p` in family 1, `j′ = 0`: `k′ − l′ = k − l`; `j′ = 2`: `k′ + l′ = k + l`;
- `p` in family 2, `j′ = 0`: `k′ + l′ = k − l − 1`; `j′ = 1`: `k′ + l′ = k + l`.

Each incidence set is `{k′ ± l′ = c}`: it has `m` points and is a graph both over `k′` and over `l′`.

**Two sum facts** (every `m ≥ 1`, `u : ZMod m → ℤ` sum-zero):

- (S1) *Same family, pullback along a row or column form.* If `v(j, k′, l′) = u(k′)` on family `j`, then the same-family part of `(G v)` at `(j, k, l)` is `(2 − m)u(k) + (m − 1)u(k) + Σ_{k′ ≠ k} u(k′) = Σ u = 0`; likewise for `u(l′)`. If `v(j, k′, l′) = u(k′ ∓ l′ + s)` (a diagonal pullback), the same-family part at `(j, k, l)` is `(2 − m)u(x) + 2(Σu − u(x)) = −m·u(x)`, with `x` the value of the form at `(k, l)`, because the row `k′ = k` and the column `l′ = l` each meet every level set of the form exactly once.
- (S2) *The parity cancellation.* For all `c ∈ ZMod m`: `Σ_x u(2x + c) + Σ_x u(2x + c + 1) = 2 Σ u = 0`, because the map `ZMod m × {0, 1} → ZMod m`, `(x, e) ↦ 2x + e`, is exactly 2-to-1. (For `m` odd each of the two sums is already `Σ u = 0`; for `m` even the two sums are over the two parity classes.)

**(W3.a)** By linearity it suffices to treat each of the eleven pieces of a datum.

- *Scalars.* `ε₁(N₀ − N₁) + ε₂(N₁ − N₂)`, and `G N_j = m·𝟙` (W1, `gram_mulVec_famVec`), so `G(N₀ − N₁) = G(N₁ − N₂) = 0`.
- *Axis pieces* `a_j(k)` or `b_j(l)` on family `j`: at a line of family `j`, (S1) gives `Σ u = 0`; at a line of another family, the entries are the sum of `u` over an incidence set, which is a graph over `k′` (resp. `l′`), so again `Σ u = 0`.
- *Overlap `w_0`* (value `w_0(k − l)` on families 0 and 1). At `(0, k, l)` with `x = k − l`: same family `−m·w_0(x)` by (S1); family 1 contributes the `m` lines with `k′ − l′ = x`, each of value `w_0(x)`: `+m·w_0(x)`. Total 0. Symmetrically at family 1. At `(2, k, l)`: the two incidence sets are `k′ + l′ = k − l − 1` (in family 0) and `k′ + l′ = k + l` (in family 1); on `k′ + l′ = c` one has `k′ − l′ = 2k′ − c`. With `c₁ = k − l − 1` and `c₂ = k + l` the entry is `Σ_{k′} w_0(2k′ − c₁) + Σ_{k′} w_0(2k′ − c₂)`; the shift `k′ ↦ k′ + l + 1` turns the second sum into `Σ_{k′} w_0(2k′ − c₁ + 1)`, so the entry is `Σ_x w_0(2x + c₀) + Σ_x w_0(2x + c₀ + 1)` with `c₀ = −c₁`, which is `0` by (S2).
- *Overlap `w_1`* (value `w_1(k + l)` on families 1 and 2). At families 1 and 2: `−m·w_1(x) + m·w_1(x) = 0` as above (the incidence set of family 1 ↔ family 2 is `k′ + l′ = k + l`). At `(0, k, l)`: the incidence sets are `k′ − l′ = k − l` (family 1) and `k′ − l′ = k + l + 1` (family 2); there `k′ + l′ = 2l′ + c`, the two `c`'s differ by `2l + 1`, and (S2) gives `0`.
- *Overlap `w_2`* (value `w_2(k + l)` on family 0 and `w_2(k − l − 1)` on family 2). At `(0, k, l)`, `x = k + l`: same family `−m·w_2(x)`; family 2 contributes the `m` lines with `k′ − l′ = k + l + 1`, where `w_2(k′ − l′ − 1) = w_2(x)`: `+m·w_2(x)`. At `(2, k, l)`, `y = k − l − 1`: same family `−m·w_2(y)`; family 0 contributes the lines `k′ + l′ = y`, of value `w_2(y)`: `+m·w_2(y)`. At `(1, k, l)`: the incidence sets are `k′ − l′ = k − l` (family 0, values `w_2(k′ + l′) = w_2(2l′ + k − l)`) and `k′ + l′ = k + l` (family 2, values `w_2(k′ − l′ − 1) = w_2(2k′ − k − l − 1)`); the two offsets `k − l` and `−k − l − 1` differ by `2k + 1`, odd, and (S2) gives `0` after a shift of the summation variable.

Hence `G · satMap(D) = 0`.

**(W3.b)** Let `D ∈ SatSrc ℤ m`, `m` odd, with `satMap D = 0`. Apply the mixed difference `(δF)(k, l) := F(k+1, l+1) − F(k+1, l) − F(k, l+1) + F(k, l)` to the family identities, as in W2: it kills `a_j(k)`, `b_j(l)` and constants, and `δ[w(k − l)] = −(Δ²w)(k − l − 1)`, `δ[w(k + l)] = (Δ²w)(k + l)`, with `(Δ²w)(z) = w(z+2) − 2w(z+1) + w(z)`. Since `m` is odd, `(k, l) ↦ (k + l, k − l)` is a bijection of `(ZMod m)²`, so family 0 gives `Δ²w_2 ≡ Δ²w_0 ≡` one integer constant `d`, and family 1 the same for `w_1`.
Now use that the coefficients are integers: along `x = 0, 1, …, m`, the first difference satisfies `(Δw)(x) = (Δw)(0) + d·x`; periodicity (`x = m` is `x = 0` in `ZMod m`) gives `d·m = 0`, so `d = 0`. Then `Δw` is a constant `e` and `Σ_{x ∈ ZMod m} (Δw)(x) = 0` gives `m·e = 0`, so `e = 0`; so each `w_i` is constant, and sum-zero gives `m·w_i = 0`, so `w_i = 0`. The family identities become `a_j(k) + b_j(l) + (constant) = 0`, so `a_j` and `b_j` are constant, hence `0` (sum-zero, `m ≠ 0` in `ℤ`), and then `ε₁ = ε₂ = 0`. So `D = 0`.

**(W3.c)** `SatSrc ℤ m` is free of rank `9(m − 1) + 2 = 9m − 7` (nine copies of the sum-zero functions, each free of rank `m − 1`, with basis `δ_x − δ_0`, `x ≠ 0`, plus `ℤ²`), and by (W3.b) `satMap` maps it isomorphically onto `SAT m`.

## Checks (run before sending)

- `m = 3, 5, 7, 9, 11, 15` (odd, including composites) and also `m = 4, 6`: the `9m − 7` basis images and 20 random admissible integer data all satisfy `G · v = 0`.
- Rank over `ℚ` of the `9m − 7` basis images: `20, 38, 56, 74, 92, 128` at `m = 3, 5, 7, 9, 11, 15` (`= 9m − 7`); at even `m = 4, 6` it is `28, 46` (`= 9m − 8`), so (W3.b) genuinely needs `m` odd.
- **Negative control:** a datum with one axis function not sum-zero is **not** in `K` at every `m` tested.

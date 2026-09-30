# The Watermark Theorem, piece W7: the discriminant of V (the final theorem)

Seventh and last piece of the Lean 4 formalization of *The Watermark Theorem*. Pieces W1–W6 are in this project (`RequestProject/Watermark/Defs.lean`, `W1.lean` … `W6.lean`, namespace `Watermark`). **Reuse their definitions and results unchanged and do not edit those files.** Put this piece in `RequestProject/Watermark/W7.lean`.

## The target

> **Theorem (The Watermark Theorem, odd-prime half).** For every prime `m ≥ 5`, the lattice `V = A ⧸ K` with the bilinear form induced by the Gram matrix of the `3m²` lines has
> **`disc V = m^{3(m−3)²}`**.

In Lean: `V m`, `formV m : LinearMap.BilinForm ℤ (V m)` (W1). The statement to prove is

**(W7.main)** For `m` prime, `5 ≤ m`: `Module.Free ℤ (V m)`, `Module.finrank ℤ (V m) = 3(m − 1)(m − 2) + 1`, and **for every `ℤ`-basis `b` of `V m`**, `(LinearMap.BilinForm.toMatrix b (formV m)).det = m ^ (3 * (m − 3) ^ 2)`.

(The determinant does not depend on the basis: a change of basis multiplies it by `det(P)² = 1`. It is positive, in agreement with the paper's sign `(−1)^{rank V − 1}`, since `rank V − 1 = 3(m − 1)(m − 2)` is even.)

## Available results (W1–W6)

- `formV_mk`: `formV [x] [y] = gramForm x y = x ⬝ᵥ G *ᵥ y` (W1).
- `finrank_K = 9m − 7` (W5); `K m` is the kernel of a map `ℤ^n → ℤ^n`, so `A ⧸ K` is torsion-free.
- `F m` (W6), with its spanning blocks `blk m β.fam β.pen` indexed by `β : FIdx m`, and the theorems `gramForm_pb_pb_of_ne`, `gramForm_famVec_pb`, `gramForm_pb_pb_self`, `gramForm_famVec_self`, `F_inf_K`, `finrank_F`, `index_F_sup_K` (W6). In words, (W6.a): the blocks are `B`-orthogonal, `B(pb u, pb v) = −m² Σ_x u(x)v(x)` inside a block, `B(N₀, N₀) = m³`, `N₀ ⊥` the blocks; (W6.b): `F ⊓ K = ⊥`, `finrank F = 3(m − 1)(m − 2) + 1`; (W6.e): the index of `F ⊔ K` in `A` is `m^{3(m²+m+2)/2 − 12}`.

## Proof

1. **V is free of the right rank.** `A ⧸ K` is finitely generated and torsion-free (if `c·x ∈ K` with `c ≠ 0` then `x ∈ K`), hence free over `ℤ`; its rank is `3m² − (9m − 7) = 3(m − 1)(m − 2) + 1`.
2. **F embeds in V with index `[A : F + K]`.** The quotient map `φ : A → V` is injective on `F` (because `F ⊓ K = ⊥`), and `V ⧸ φ(F) ≅ A ⧸ (F + K)`. So `φ(F)` is a full-rank sublattice of `V` of index `N := m^{3(m²+m+2)/2 − 12}`.
3. **Change of basis.** Let `c` be the basis of `φ(F)` given by the images of the spanning vectors of `F`: for each spanning block, the `m − 1` vectors `pb j π (δ_x − δ_0)`, `x ≠ 0`, and `famVec m 0`. For any basis `b` of `V`, with `P` the matrix of `c` in `b`: `Gram_c = Pᵀ · Gram_b · P`, and `|det P| = [V : φ(F)] = N`. Hence `det Gram_c = N² · det Gram_b`.
4. **The Gram determinant of F.** By (W6.a), `Gram_c` is block diagonal: `3(m − 2)` blocks equal to `−m² (I + J)` of size `m − 1` (the standard Gram of `δ_x − δ_0` is `I + J`, of determinant `m`), and the `1 × 1` block `m³`. So
   `det Gram_c = ((−m²)^{m−1} · m)^{3(m−2)} · m³ = m^{3(m−2)(2m−1) + 3}`
   (the sign is `+` because `(m − 1)` is even).
5. **Arithmetic.** `det Gram_b = m^{3(m−2)(2m−1) + 3} / m^{3(m²+m+2) − 24}`, and
   `3(m − 2)(2m − 1) + 3 − 3(m² + m + 2) + 24 = 3m² − 18m + 27 = 3(m − 3)²`.

## Checks (run before sending)

- `m = 5, 7`: `det Gram_c = 5^84`, `7^198` (exact integer determinant of the `B`-Gram of the spanning vectors of `F`: `37`, `91` vectors); the index `[A : F + K] = 5^36`, `7^75` (Macaulay2, with an integer basis of `K`); hence `det Gram_b = 5^{84 − 72} = 5^12` and `7^{198 − 150} = 7^48`.
- Independently: the product of the non-zero elementary divisors of `G` (Smith form, Macaulay2) is `5^12` at `m = 5` and `7^48` at `m = 7`, which is `|disc V|` by a separate argument; both match `m^{3(m−3)²}`.

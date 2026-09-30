# The Watermark Theorem, piece W6: the sublattice F, its Gram matrix, and the index [A : F + K]

Sixth piece of the Lean 4 formalization of *The Watermark Theorem*. Pieces W1–W5 are in this project (`RequestProject/Watermark/Defs.lean`, `W1.lean` … `W5.lean`, namespace `Watermark`). **Reuse their definitions and results unchanged and do not edit those files.** Put this piece in `RequestProject/Watermark/W6.lean`.

## Setting (from W1–W5)

`G = gram m`, the form `gramForm m` (`B(x, y) = x ⬝ᵥ G *ᵥ y`), `K m = ker G`, `famVec`, `pencil`, `sumZero ℤ m`, `SAT m`, `pb j π u` (pullback of `u` along pencil `π` on family `j`), and the results: `SAT_le_K`, `finrank_SAT` (W3), the formulas for `G *ᵥ pb` and `sum_pencil_mul_pencil`, `sum_pencil_mul_same` (W4), `finrank_K` (`finrank ℤ K = 9m − 7`) and `index_SAT` (`((SAT m).comap (K m).subtype).toAddSubgroup.index = m ^ 12`) (W5).

Throughout, `m` is prime and `m ≥ 5`. Pencil `t` means `pencil (some t)`; pencil `∞` is `none`. A pencil is **live non-overlap** if it is `some t` with `t ∉ {0, 1, −1}` (there are `m − 3` on each family).

**The block of a pencil.** `blk j π : Submodule ℤ (A m)` is the image of `sumZero ℤ m` under `u ↦ pb j π u`.

**F.** `F m : Submodule ℤ (A m)` is the sum of
- `blk j (some t)` for every family `j` and every live non-overlap `t` (`3(m − 3)` blocks),
- `blk 0 (some (−1))`, `blk 1 (some 1)`, `blk 0 (some 1)` (one member of each overlap pair),
- `ℤ · famVec m 0`.

**L.** `Lfam m : Submodule ℤ (Point m → ℤ)` is the span of the constant function `1` and of all `u ∘ pencil π` with `π : Option (ZMod m)` and `u ∈ sumZero ℤ m`. `L m : Submodule ℤ (A m)` is `{x | ∀ j, restrict x j ∈ Lfam m}`.

## Statements

**(W6.a) The Gram matrix of F.** For `u, v ∈ sumZero ℤ m`:
1. two different blocks among those spanning `F` are `B`-orthogonal, and `B(famVec m 0, pb j π u) = 0` for each of them;
2. inside one block, `B(pb j π u, pb j π v) = −m² · Σ_x u(x) v(x)`;
3. `B(famVec m 0, famVec m 0) = m³`.

**(W6.b) F meets K trivially:** `F m ⊓ K m = ⊥`. Moreover `Module.finrank ℤ (F m) = 3(m − 1)(m − 2) + 1`.

**(W6.c) The index of one family.** The index of `Lfam m` in `Point m → ℤ` is `m ^ ((m² + m + 2)/2)`.

**(W6.d) F + SAT = L**, hence the index of `F m ⊔ SAT m` in `A m` is `m ^ (3(m² + m + 2)/2)`.

**(W6.e) The index [A : F + K]:** the index of `F m ⊔ K m` in `A m` is `m ^ (3(m² + m + 2)/2 − 12)`.

## Proofs

**(W6.a)** `B(x, y) = x ⬝ᵥ (G *ᵥ y)`. By W4, for each spanning block `G *ᵥ pb j π v` is `−m • pb j π v` plus, for the three overlap members, `m •` a pullback on a *different* family along an overlap pencil of that family. So for two spanning blocks:
- on different families, `pb j π u` and `G *ᵥ pb j′ π′ v` have disjoint supports, except for the overlap partner term; but an overlap partner lives on the partner family along pencil `±1`, and the only spanning block on that family along that pencil would be the partner itself, which is not in `F` (only one member of each pair is). Check: the partner of `blk 0 (−1)` is on family 1 at pencil `−1`; of `blk 1 (1)` on family 2 at pencil `1`; of `blk 0 (1)` on family 2 at pencil `−1`. None of these three is a spanning block of `F`, and a pullback along a different pencil of the same family is orthogonal by the next point.
- on the same family and different pencils: `pb j π u ⬝ᵥ pb j π′ v = (Σu)(Σv) = 0` (W4, `sum_pencil_mul_pencil`).
- with `famVec m 0`: `B(N₀, y) = (G *ᵥ N₀) ⬝ᵥ y = m · Σ_p y(p)`, and the sum of a pullback of a sum-zero function is `m · Σ u = 0`.
Inside one block: `B(pb u, pb v) = pb u ⬝ᵥ (−m • pb v + partner) = −m · (m Σ_x u(x)v(x))` (W4, `sum_pencil_mul_same`; the partner is on another family). And `B(N₀, N₀) = m · (number of lines of family 0) = m · m² = m³`.

**(W6.b)** Let `x ∈ F ⊓ K`, `x = Σ_β x_β + c·famVec m 0` with `x_β` in the spanning blocks. Since `x ∈ K`, `B(x, x_β) = 0` for each `β` and `B(x, famVec m 0) = 0`. By (W6.a) `B(x, x_β) = B(x_β, x_β) = −m²‖u_β‖² ` (`x_β = pb u_β`), so `u_β = 0`, and `B(x, N₀) = c·m³` gives `c = 0`. The rank: each block is isomorphic to `sumZero ℤ m` (rank `m − 1`, `pb` injective because the pencil is surjective), the blocks are independent (the argument just given), and there are `3(m − 3) + 3 = 3(m − 2)` of them plus one: `3(m − 2)(m − 1) + 1`.

**(W6.c)** A basis of `Lfam`: for each of the `m + 1` pencils the `m − 1` functions `(δ_x − δ_0) ∘ pencil π` (`x ≠ 0`), and the constant `1`; that is `m²` vectors in `Point m → ℤ ≅ ℤ^{m²}`. Their standard Gram matrix is block diagonal: two pencils are orthogonal (W4.a), inside a pencil the Gram is `m · (I + J)` of size `m − 1` (determinant `m^{m−1} · m`), and `⟨1, 1⟩ = m²`. So the Gram determinant is `(m^m)^{m+1} · m² = m^{m² + m + 2}`, and the index of the span of a square integer matrix `M` of full rank is `|det M| = √(det M Mᵀ) = m^{(m²+m+2)/2}` (`m² + m` is even).

**(W6.d)** `F ⊆ L` and `SAT ⊆ L` (every generator restricts on each family to a combination of pullbacks and constants). Conversely `L` is generated by the vectors `pb j π u` (all `j`, `π`, `u ∈ sumZero`) and `famVec m j`, and each is in `F + SAT`: live non-overlap blocks are in `F`; axis blocks are in `SAT` (datum with one `a_j` or `b_j`); for an overlap pair, one member is in `F` and member + partner is in `SAT` (datum with one `w_i`: `w_0` gives `pb 0 (−1) u + pb 1 (−1) u`, `w_1` gives `pb 1 (1) u + pb 2 (1) u`, `w_2` gives `pb 0 (1) u + pb 2 (−1) u⁻`, and `u ↦ u⁻` is a bijection of `sumZero`); `famVec m 0 ∈ F` and `famVec m 0 − famVec m 1`, `famVec m 1 − famVec m 2 ∈ SAT` (the scalars `ε₁`, `ε₂`). So `F + SAT = L`, and `[A : L] = [ℤ^{Point} : Lfam]³`.

**(W6.e)** `L = F + SAT ⊆ F + K ⊆ A`, so `[A : L] = [A : F + K] · [F + K : F + SAT]`. The map `K → (F + K)/(F + SAT)` is surjective with kernel `K ∩ (F + SAT) = SAT` (if `k = f + s` then `f = k − s ∈ F ∩ K = 0`), so `[F + K : F + SAT] = [K : SAT] = m¹²` (W5). Hence `[A : F + K] = m^{3(m²+m+2)/2} / m¹²`.

## Checks (run before sending)

- `m = 5, 7, 11`: the index of `Lfam` is `5^16`, `7^29`, `11^67` (exact integer determinant).
- `m = 5, 7`: `F` has `37`, `91` generators; `|det|` of the `3m² × 3m²` matrix of the generators of `F` and of `SAT` is `5^48`, `7^87` exactly (so `F + SAT = L` and `F ∩ SAT = 0`); `|det B|_F| = 5^84`, `7^198`; and, by Macaulay2 with an integer basis of `K`, `[A : F + K] = 5^36`, `7^75` (predicted `m^{3(m²+m+2)/2 − 12}`).

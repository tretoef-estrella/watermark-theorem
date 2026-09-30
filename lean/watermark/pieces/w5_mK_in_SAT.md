# The Watermark Theorem, piece W5: the kernel census, mK ⊆ SAT, and [K : SAT] = m¹²

Fifth piece of the Lean 4 formalization of *The Watermark Theorem*. Pieces W1–W4 are in this project (`RequestProject/Watermark/Defs.lean`, `W1.lean` … `W4.lean`, namespace `Watermark`). **Reuse their definitions and results unchanged and do not edit those files.** Put this piece in `RequestProject/Watermark/W5.lean`.

## Setting (from W1–W4)

`G = gram m` (symmetric: `gram_transpose`), `K m = ker G ⊆ A m`, `restrict x j : Point m → ℤ`, `aug`, `famVec`, `pencil`, `sumZero ℤ m`; `SatData`, `SatSrc`, `satMap`, `SAT m` (W2); `SAT_le_K`, `finrank_SAT` (W3); `pb`, `fib`, `ext`, the formulas for `G · pb` and `smul_ext_eq_sum_pb_fib` (W4); `aug_of_mem_K` (W1: `Σ_j aug(x_j) = 0` and `m ∣ aug(x_j)`); Lemma C (W2: `finrank_range_satMap = 9m − 19` over `ZMod m`, `satMap_red`, `exists_satSrc_lift`).

Throughout, `m` is prime and `m ≥ 5`. Pencil `t` means `pencil (some t)`.

## Statements

Let `x ∈ K m` and write `x_j := restrict x j`.

**(W5.a) Census (paper, kernel census / R.3).**
1. For every `j` and every `t ∉ {0, 1, −1}`, `fib (some t) x_j` is constant.
2. `fib (some (−1)) x_0 − fib (some (−1)) x_1` is constant; `fib (some 1) x_1 − fib (some 1) x_2` is constant; and `v ↦ fib (some 1) x_0 (v) − fib (some (−1)) x_2 (v + 1)` is constant.

**(W5.b) mK ⊆ SAT (paper, R.4).** `(m : ℤ) • x ∈ SAT m` for every `x ∈ K m`.

**(W5.c) Rank.** `Module.finrank ℤ (K m) = 9m − 7`.

**(W5.d) Index (paper, R.5 and Lemma C).** The index of `SAT m` in `K m` is `m ^ 12`; for instance `((SAT m).comap (K m).subtype).toAddSubgroup.index = m ^ 12` (any equivalent formulation of «`[K : SAT] = m¹²`» is fine).

## Proofs

**(W5.a)** For `u ∈ sumZero ℤ m` and any `v : A m`, symmetry of `G` gives `x ⬝ᵥ (G *ᵥ v) = (G *ᵥ x) ⬝ᵥ v = 0`. And `x ⬝ᵥ pb j π u = Σ_v u(v) · fib π x_j (v)` (group the points of family `j` by the value of the pencil).
1. With `v = pb j (some t) u` and W4 (`G *ᵥ pb = −m • pb`): `−m · Σ_v u(v) fib(v) = 0`, so `Σ_v u(v) fib(v) = 0` for every sum-zero `u`. Taking `u = δ_a − δ_b` gives `fib(a) = fib(b)`.
2. With `v = pb 0 (−1) u`: `G *ᵥ v = −m • pb 0 (−1) u + m • pb 1 (−1) u`, so `Σ_v u(v)·(fib_{0,−1}(v) − fib_{1,−1}(v)) = 0` for every sum-zero `u`, hence the difference is constant. Same with `pb 1 (1) u` for the pair (1,2). With `pb 0 (1) u`: `G *ᵥ v = −m • pb 0 (1) u + m • pb 2 (−1) u⁻`, `u⁻(y) = u(y − 1)`, and `Σ_y u(y − 1) fib_{2,−1}(y) = Σ_v u(v) fib_{2,−1}(v + 1)`, so `Σ_v u(v)(fib_{0,1}(v) − fib_{2,−1}(v + 1)) = 0`.

**(W5.b)** Put `μ_j := aug(x_j)/m ∈ ℤ` (W1: `m ∣ aug(x_j)`, and `Σ_j μ_j = 0`). For each `j` and pencil `π`, `Σ_v fib π x_j (v) = aug(x_j)`; put `f̃_{j,π} := fib π x_j − μ_j`, a sum-zero integer function. By W4 (W4.c),
`m • ext j x_j = Σ_π pb j π (fib π x_j) − aug(x_j) • famVec m j = Σ_π pb j π f̃_{j,π} + μ_j • famVec m j`
(the `m + 1` constants `μ_j` give `(m + 1)μ_j • famVec m j`, and `aug(x_j) = mμ_j`). By (W5.a), `f̃_{j,t} = 0` for the live non-overlap pencils (a constant sum-zero function is 0, since `m ≠ 0` in `ℤ`), and the overlap differences, being constant and sum-zero, vanish:
`f̃_{0,−1} = f̃_{1,−1}`, `f̃_{1,1} = f̃_{2,1}`, `f̃_{2,−1}(y) = f̃_{0,1}(y − 1)`.
Now define the datum `D`:
- `a_j := f̃_{j, some 0}` (pencil `0` is `k`), `b_j := f̃_{j, none}` (pencil `∞` is `l`);
- `w_0 := f̃_{0,−1}`, `w_1 := f̃_{1,1}`, `w_2 := f̃_{0,1}`;
- `ε₁ := μ_0`, `ε₂ := −μ_2` (so `ε₂ − ε₁ = μ_1`).
All nine functions are sum-zero, so `D ∈ SatSrc ℤ m`, and summing the three family identities, `satMap ℤ m D = m • x` (on family 2 the term `pb 2 (−1) f̃_{2,−1}` is `w_2(k − l − 1)`, as in `satMap`). Hence `m • x ∈ SAT m`.

**(W5.c)** `SAT m ≤ K m` (W3) and `m • K m ≤ SAT m` (W5.b), with `m ≠ 0`, so `K` and `SAT` have the same rank; `finrank SAT = 9m − 7` (W3).

**(W5.d)** Three facts.
1. `K m ∩ m·A = m·K m`: if `G(m y) = 0` then `G y = 0` (`ℤ` is torsion-free).
2. By (W5.b), `K/SAT` is killed by `m`, so it is an `F_m`-vector space and `|K/SAT| = m^{dim}`, with `dim = dim_{F_m}(K/mK) − dim_{F_m}(SAT/mK) = (9m − 7) − dim_{F_m}(SAT/mK)` (`K` is free of rank `9m − 7` by (W5.c)).
3. By fact 1, `K/mK ↪ A/mA`, and it sends `SAT/mK` onto the image of `SAT` in `A/mA = (Line m → ZMod m)`. That image is `red(satMap ℤ m (SatSrc ℤ m)) = satMap (ZMod m) m (SatSrc (ZMod m) m)` (W2: `satMap_red` and `exists_satSrc_lift`), whose dimension is `9m − 19` (W2, Lemma C).

Hence `dim_{F_m} K/SAT = (9m − 7) − (9m − 19) = 12` and `[K : SAT] = m¹²`.

## Checks (run before sending)

- `m = 5, 7`: for every vector of an integer basis of `K = ker G` (Macaulay2, `gens ker G`: 38 and 56 vectors), the census (W5.a) holds, and the datum `D` of the proof is admissible with `satMap D = m·x` exactly.
- `m = 5`: `[K : SAT] = 5¹²` computed directly (Macaulay2, determinant of the coordinates of the SAT basis in a basis of `K`); `rank K = 38, 56` at `m = 5, 7`.

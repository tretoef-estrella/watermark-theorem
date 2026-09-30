# The Watermark Theorem, piece W2: the saturation lattice SAT and Lemma C (the counting lemma, d = 12)

This is the second piece of the Lean 4 formalization of *The Watermark Theorem* (R. Amichis Luengo, 2026). Piece W1 is already in this project: `RequestProject/Watermark/Defs.lean` and `RequestProject/Watermark/W1.lean`, namespace `Watermark`. **Reuse its definitions unchanged** (`Point m`, `Line m`, `gram m`, `A m`, `K m`, `V m`, `famVec`, `aug`, `restrict`, `pencil`, `E`) and do not edit those two files. Put this piece in a new file, `RequestProject/Watermark/W2.lean`, importing them.

## Setting

Let `m` be a natural number (`[NeZero m]`; where stated, `m` prime and `m ≥ 5`). Lines are `(j, k, l) ∈ Fin 3 × ZMod m × ZMod m`, as in W1.

**The data.** For a commutative ring `R`, a *SAT datum* over `R` consists of

- for each family `j ∈ Fin 3`, two functions `a_j, b_j : ZMod m → R` (the two axis pencils `k` and `l` of family `j`);
- three functions `w_0, w_1, w_2 : ZMod m → R` (the three overlap pencils: `w_0` serves the pair of families (0,1), `w_1` the pair (1,2), `w_2` the pair (0,2));
- two scalars `ε₁, ε₂ ∈ R`.

A datum is *admissible* if all nine functions are **sum-zero**: `Σ_{x ∈ ZMod m} f(x) = 0`. The admissible data form an `R`-submodule `SatSrc R` of the module of all data. (Any convenient encoding is fine, e.g. `(Fin 3 → ZMod m → R) × (Fin 3 → ZMod m → R) × (Fin 3 → ZMod m → R) × (R × R)` with the submodule cut out by the nine sum-zero conditions.)

**The map.** `satMap R : data → (Line m → R)` is the `R`-linear map

- family 0: `(0, k, l) ↦ a_0(k) + b_0(l) + w_0(k − l) + w_2(k + l) + ε₁`;
- family 1: `(1, k, l) ↦ a_1(k) + b_1(l) + w_0(k − l) + w_1(k + l) + (ε₂ − ε₁)`;
- family 2: `(2, k, l) ↦ a_2(k) + b_2(l) + w_1(k + l) + w_2(k − l − 1) − ε₂`.

(In the paper's language, §7: the six axis pullback blocks, the three paired overlap blocks — the pair (0,2) with the translation `τ`, here `x ↦ x − 1` — and `ε₁(N₀ − N₁) + ε₂(N₁ − N₂)`.)

**SAT.** Over `ℤ`: `SAT m : Submodule ℤ (A m)` is the image of `SatSrc ℤ` under `satMap ℤ`. (Later pieces prove `SAT m ≤ K m` and use `SAT`; in this piece only define it.)

**Reduction mod m.** Write `red : ℤ → ZMod m` for the cast, applied pointwise to functions and data.

## Statements

**(W2.a)** `finrank (ZMod m) {f : ZMod m → ZMod m | Σ_x f(x) = 0} = m − 1` for `m ≥ 1`; hence `finrank (ZMod m) (SatSrc (ZMod m)) = 9(m − 1) + 2 = 9m − 7`. (For the finrank, `m` prime so that `ZMod m` is a field.)

**(W2.b) Compatibility.** For every datum `D` over `ℤ`, `red ∘ satMap ℤ D = satMap (ZMod m) (red D)`; and `red` maps `SatSrc ℤ` onto `SatSrc (ZMod m)` (every sum-zero `f : ZMod m → ZMod m` is the reduction of a sum-zero `y : ZMod m → ℤ`).

**(W2.c) Lemma C (paper §9).** Let `m ≥ 5` be prime. Then

- `finrank (ZMod m) (ker (satMap (ZMod m) restricted to SatSrc (ZMod m))) = 12`, and
- `finrank (ZMod m) (range (satMap (ZMod m) restricted to SatSrc (ZMod m))) = 9m − 19`.

## Proofs

Work over `F := ZMod m`, `m ≥ 5` prime. Both finranks of (W2.c) follow from the first by rank–nullity and (W2.a).

**(W2.a)** The sum map `(ZMod m → F) → F` is surjective (the indicator of `0` has sum 1), so its kernel has dimension `m − 1`.

**(W2.b)** The first part is immediate from the formula (the cast is a ring map). For the lift: given `f`, take any `y₀ : ZMod m → ℤ` reducing to `f` (e.g. `x ↦ (f x).val`), and subtract `(Σ y₀)/m` at the point `0`; `m` divides `Σ y₀` because the sum reduces to `Σ f = 0`.

**(W2.c)** We describe the kernel exactly. Let `D` be an admissible datum with `satMap D = 0`, and write `F_j(k, l) = 0` for the three family identities.

*Step 1 (mixed differences kill the axis terms).* For a function `F : ZMod m × ZMod m → F` put `(δF)(k, l) := F(k+1, l+1) − F(k+1, l) − F(k, l+1) + F(k, l)`. Then `δ` kills every function of `k` alone, of `l` alone, and constants. For a function `w` of one variable put `(Δ²w)(z) := w(z+2) − 2w(z+1) + w(z)`. A direct computation gives

- `δ[(k, l) ↦ w(k − l)] (k, l) = −(Δ²w)(k − l − 1)`;
- `δ[(k, l) ↦ w(k + l)] (k, l) = (Δ²w)(k + l)`.

*Step 2 (the second differences are one common constant).* Applying `δ` to family 0: `(Δ²w_2)(k + l) = (Δ²w_0)(k − l − 1)` for all `k, l`. Since `m` is odd, `(k, l) ↦ (k + l, k − l)` is a bijection of `(ZMod m)²`, so `(Δ²w_2)(x) = (Δ²w_0)(y)` for all `x, y`: both are the same constant. Family 1 gives the same for `w_0` and `w_1`; family 2 for `w_1` and `x ↦ w_2(x − 1)`, whose second difference is a translate of `Δ²w_2`. Hence `Δ²w_0 = Δ²w_1 = Δ²w_2 = 2c` for one constant `c ∈ F` (`2` is invertible).

*Step 3 (so the w's are quadratics with a common leading coefficient).* If `Δ²w ≡ 2c`, then `x ↦ w(x) − c x²` has zero second difference, so its first difference is constant, so it is `α x + β`: `w(x) = c x² + α x + β`. (Iterate over `x = 0, 1, …, m − 1`; no consistency condition is needed because `w` is given.) So `w_i(x) = c x² + α_i x + β_i`, `i = 0, 1, 2`.

*Step 4 (the axis functions are then determined up to a split).* With these `w`'s, the non-axis part of each family identity is a function of `k` plus a function of `l`, because the cross terms `kl` cancel:
`(k − l)² + (k + l)² = 2k² + 2l²` (families 0 and 1), and `(k + l)² + (k − l − 1)² = 2k² + 2l² − 2k + 2l + 1` (family 2).
So each family identity reads `a_j(k) + b_j(l) = P_j(k) + Q_j(l)` for explicit quadratics `P_j, Q_j` (depending on `c, α, β, ε`), whose solutions are exactly `a_j = P_j + t_j`, `b_j = Q_j − t_j`, `t_j ∈ F` (set `l = 0`, then `k = 0`).

*Step 5 (every such choice is admissible, and the count is 12).* A quadratic `x ↦ c x² + α x + β` on `ZMod m` is sum-zero when `m ≥ 5` is prime: `Σ_x 1 = m = 0`, `Σ_x x = m(m−1)/2 = 0` (`m` odd), and `Σ_x x² = (m−1)m(2m−1)/6 = 0` because `gcd(m, 6) = 1`. So all nine functions of Steps 3–4 are sum-zero, and the kernel is the image of the injective linear map
`(c, α_0, α_1, α_2, β_0, β_1, β_2, ε₁, ε₂, t_0, t_1, t_2) ∈ F^12 ↦ D`.
(Injective: `c, α_i, β_i` are read off the `w_i`; `ε₁, ε₂` are part of `D`; each `t_j` is read off `a_j(0)` once the rest is fixed.) Hence the kernel has dimension 12.

*(This is the paper's Lemma C. The paper argues with the polynomial–function dictionary on `F_m`; the finite-difference route above proves the same statement. `m = 3` is excluded because there `Σ x² ≠ 0`, so a quadratic is not sum-zero and the count drops to 11.)*

## Checks (run before sending)

- `m = 3, 5, 7, 11`: with the (0,2) translation `x ↦ x − 1`, the integer SAT generators lie in `K` (`G · v = 0` for all `9m − 7` of them); every other shift fails; swapping the pencils of the (0,2) pair fails (negative controls).
- `m = 5, 7, 11`: rank over `ℚ` of the generators `= 9m − 7` (`38, 56, 92`); rank mod `m` `= 9m − 19` (`26, 44, 80`); kernel mod `m` `= 12`.
- Solving the family identities directly as a linear system over `F_m` in the nine functions and two scalars: the solution space has dimension `12` at `m = 5, 7, 11, 13`, and every basis solution has `w_i` with zero third difference and one common second difference (the route of Steps 2–3). **Control:** `m = 3` gives `11`.

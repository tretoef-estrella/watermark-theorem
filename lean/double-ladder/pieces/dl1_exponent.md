# The Double Ladder Theorem, piece DL1: the exponent of the discriminant group divides m²

This is the first piece of the Lean 4 formalization of *The Double Ladder Theorem*, the companion of *The Watermark Theorem*. The Watermark Theorem is already formalized in this project: `RequestProject/Watermark/Defs.lean`, `W1.lean` … `W7.lean`, namespace `Watermark`. **Reuse its definitions and results unchanged, and do not edit those files.** Put this piece in `RequestProject/DoubleLadder/DL1.lean`, namespace `DoubleLadder`.

## What the whole theorem says, and where this piece sits

For a prime `m ≥ 7`, the discriminant group of the lattice `V` of the lines on the Fermat surface of degree `m` is
`V*/V ≅ (ℤ/m)^{3m²−24m+59} × (ℤ/m²)^{3m−16}`.

The proof has three parts:
1. the order `m^{3(m−3)²}`, which is W7 (done);
2. **the exponent divides `m²` (this piece)**;
3. the rank of `G` modulo `m` equals `12(m−3)` (a later piece).

Together they force the profile, because `#(cyclic factors) = rank V − rank(G mod m)` and `a + 2b = 3(m−3)²`.

## Setting (from W1–W7)

- `Point m = ZMod m × ZMod m` and `Line m = Fin 3 × Point m`.
- `gram m` is the matrix `G` and `A m = Line m → ℤ`.
- `K m` is the kernel of `G`, `V m = A m ⧸ K m`, and `formV m` is the induced form, with `formV_mk : formV m [x] [y] = gramForm m x y = x ⬝ᵥ (G *ᵥ y)`.
- `famVec m j` and `ones m`.
- `pencil : Option (ZMod m) → Point m → ZMod m`, where `some t ↦ (k, l) ↦ k + t·l` and `none ↦ (k, l) ↦ l`. So `some 0` is `k`, `none` is `l`, `some 1` is `k + l`, and `some (−1)` is `k − l`.
- `pb j π u` (W4) and `sumZero ℤ m` (W2).
- Results used:
  - `gram_mulVec_famVec : G *ᵥ famVec m j = m • ones m` (W1);
  - the formulas of W4 for `G *ᵥ pb j π u`, `u ∈ sumZero`: `gram_mulVec_pb_axis_some_zero`, `gram_mulVec_pb_axis_none`, `gram_mulVec_pb_live`, and the six overlap formulas `gram_mulVec_pb_zero_neg_one` … `gram_mulVec_pb_two_neg_one`;
  - `sum_pencil_mul_pencil`, `sum_pencil_mul_same`, `smul_ext_eq_sum_pb_fib` (W4);
  - `watermark_theorem` (W7): `V m` is free of rank `3(m−1)(m−2)+1`, and `det (toMatrix b (formV m)) = m^{3(m−3)²}` for every basis `b`.

## The certificate matrix

Define `Y := ylad m : Matrix (Line m) (Line m) ℤ`, block-diagonal over the three families:

```
def ylad (m : ℕ) : Matrix (Line m) (Line m) ℤ := Matrix.of fun p q =>
  if p.1 = q.1 then
      (if p.2.1 = q.2.1 then 1 else 0) + (if p.2.2 = q.2.2 then 1 else 0)
    + 3 * (if p.2.1 - p.2.2 = q.2.1 - q.2.2 then 1 else 0)
    + 3 * (if p.2.1 + p.2.2 = q.2.1 + q.2.2 then 1 else 0)
    - (if p = q then 6 * (m : ℤ) else 0)
  else 0
```

In words: inside each family, `Y = P_k + P_l + 3 P_{k−l} + 3 P_{k+l} − 6m·I`, where `P_π(p, q) = 1` iff the pencil `π` takes the same value at `p` and `q`.

## Statements

**(DL1.a) The certificate identity.** For `m` prime with `5 ≤ m`:
`gram m * ylad m * gram m = (6 * (m : ℤ) ^ 2) • gram m`.

**(DL1.b) The exponent, in coordinates.** For `m` prime with `5 ≤ m` and every `ℤ`-basis `b : Module.Basis ι ℤ (V m)` (`Fintype ι`, `DecidableEq ι`), with `M := LinearMap.BilinForm.toMatrix b (formV m)`:
`∃ X : Matrix ι ι ℤ, M * X = ((m : ℤ) ^ 2) • (1 : Matrix ι ι ℤ)`.

**(DL1.c) (welcome) The exponent, intrinsically.** For `m` prime with `5 ≤ m`: for every `f : Module.Dual ℤ (V m)` there is `v : V m` with `((m : ℤ) ^ 2) • f = formV m v`, i.e. `m²·V* ⊆ V`.

Weaker hypotheses are welcome where the proof allows: (DL1.a) needs only `m` odd, prime, `m ≥ 5`.

## Proof

### Step 1. `Y` on the pieces of W4
Take `u ∈ sumZero ℤ m`. On a single family, `P_π (pb j π′ u)`:
- equals `m • pb j π u` if `π′ = π`, because each fibre of a pencil has `m` points (`sum_pencil_mul_same`);
- equals `0` if `π′ ≠ π`: two distinct pencils are independent coordinates, so each fibre of `π` meets each fibre of `π′` in exactly one point, and `Σu = 0` (`sum_pencil_mul_pencil`).

The four pencils `some 0, none, some (−1), some 1` are pairwise distinct because `m` is odd. Hence, for every `j`:
- **axis pencils** (`π = some 0` or `none`): `Y *ᵥ pb j π u = (1 − 6)m • pb j π u = −5m • pb j π u`;
- **overlap pencils** (`π = some 1` or `some (−1)`): `Y *ᵥ pb j π u = (3 − 6)m • pb j π u = −3m • pb j π u`;
- **live pencils** (`π = some t`, `t ∉ {0, 1, −1}`): `Y *ᵥ pb j π u = −6m • pb j π u`;
- **family vectors:** `Y *ᵥ famVec m j = (1+1+3+3−6)m • famVec m j = 2m • famVec m j`.

It follows that `Y *ᵥ ones m = 2m • ones m`.

### Step 2. `G Y G = 6m² G` on each piece
Recall W4 (for `u ∈ sumZero`) and W1.
- **Axis:** `G *ᵥ pb j π u = 0`, so both sides are `0`.
- **Live:** `G v = −m v` for `v = pb j (some t) u`. Then `G Y G v = G Y (−m v) = G(6m² v) = −6m³ v = 6m² G v`.
- **Overlap pairs:** take `v = pb 0 (−1) u` and `v′ = pb 1 (−1) u`, so that `G v = −m v + m v′` and `G v′ = −m v′ + m v`. Then
  - `Y G v = −3m(−m v + m v′) = 3m² (v − v′)`;
  - `G(3m²(v − v′)) = 3m²(−2m v + 2m v′) = 6m²(−m v + m v′) = 6m² G v`.

  The pair `(1, some 1)`, `(2, some 1)` is the same. For the pair `(0, some 1)`, `(2, some (−1))` use the shifted formulas: `G pb 0 (1) u = −m pb 0 (1) u + m pb 2 (−1) u⁻` and `G pb 2 (−1) u⁻ = −m pb 2 (−1) u⁻ + m pb 0 (1) u`, since `(u⁻)⁺ = u`; the same computation gives `6m² G`. Here `u⁻ = fun x => u (x − 1)` is again in `sumZero`.
- **Family vectors:** `G famVec j = m • ones`, `Y ones = 2m • ones`, and `G ones = Σ_j G famVec j = 3m • ones`. So `G Y G famVec j = G(2m² ones) = 6m³ ones = 6m² G famVec j`.

### Step 3. From the pieces to all of A
It suffices to prove `G *ᵥ (Y *ᵥ (G *ᵥ x)) = 6m² • (G *ᵥ x)` for every `x : A m`; the matrix identity then follows by evaluating at the basis vectors (`Matrix.ext` via `mulVec_single`, or `Matrix.toLin'` injectivity). Since `A m` is torsion-free over `ℤ`, it suffices to prove it for `m² • x`.

Write `x = Σ_j ext j (restrict x j)`. By `smul_ext_eq_sum_pb_fib`, `m • ext j y = Σ_π pb j π (fib π y) − (Σ y) • famVec m j`. For each `w = fib π y`, `m • w = (m • w − (Σ w) • 1) + (Σ w) • 1`, where the first term is in `sumZero` and `pb j π (fun _ => 1) = famVec m j`. So `m² • x` is a `ℤ`-combination of vectors `pb j π u` with `u ∈ sumZero` and of the `famVec m j`, and Step 2 applies to each of them. (Every pencil `π : Option (ZMod m)` falls in exactly one of the classes axis, overlap or live.)

### Step 4. (DL1.b)
Let `φ = (K m).mkQ : A m → V m`, and let `P : Matrix ι (Line m) ℤ` be the matrix of `φ` in the basis `b` (column `p` = coordinates `b.repr (φ (single p 1))`). By `formV_mk`, `G = Pᵀ * M * P`. Since `φ` is surjective, pick `Q : Matrix (Line m) ι ℤ` with `P * Q = 1` (a preimage of each basis vector). From (DL1.a), `Pᵀ M P Y Pᵀ M P = 6m² Pᵀ M P`; multiplying by `Qᵀ` on the left and `Q` on the right gives `M Z M = 6m² M` with `Z := P * Y * Pᵀ`, an integer matrix.

`det M = m^{3(m−3)²} ≠ 0` (W7), so `M` is invertible over `ℚ` and `M Z = 6m² · 1`. Multiply on the left by `adjugate M`: `m^N • Z = 6m² • adjugate M`, with `N = 3(m−3)²`. Every entry of `m^N • Z` is divisible by `6`, and `gcd(6, m) = 1` (`m` is a prime `≥ 5`), so every entry of `Z` is divisible by `6`. Take `X := Z / 6` (entrywise exact division). Then `M X = m² · 1`.

### Step 5. (DL1.c)
Given `f`, let `c := b.repr`-coordinates of `f` (`c i = f (b i)`) and `v := Σ_i (X *ᵥ c) i • b i`. Then `formV m v (b i) = (M X c)_i = m² c_i` (`M` is symmetric by `formV_symm`/`gram_transpose`), so `formV m v = m² • f` on the basis, hence everywhere.

## Checks (run before sending)

- `m = 5, 7, 11, 13, 17`: `G Y G = 6m² G` holds exactly as integer matrices.
  - Controls: `G Y G ≠ 6m G`.
  - With the weights `(1, 1, 1, 1)` in place of `(1, 1, 3, 3)`, `G Y G` is not a multiple of `G` (checked at `m = 5, 7`).
- Step 1, entry by entry, at `m = 5, 7, 11, 13`: `Y` acts by `−5m` (axis), `−3m` (overlap), `−6m` (the live pencil `k + 2l`) on `pb j π (δ₁ − δ₀)` for every family, and by `2m` on `famVec`.
- The elementary-divisor profile of `G` over `ℤ_{(m)}` has no divisor of valuation `3` at `m = 5, 7, 11, 13`, and 9m − 7 infinite ones (the kernel). The profiles `{0: 26, 1: 10, 2: 1}`, `{0: 48, 1: 38, 2: 5}`, `{0: 96, 1: 158, 2: 17}`, `{0: 120, 1: 254, 2: 23}` agree with the Double Ladder law, `m = 13` included.
- Why `Y` works: `G` has minimal polynomial `x(x + m)(x + 2m)(x − 3m)` (checked at `m = 5 … 17`). `Y` acts as `6m²/λ` on the `λ`-eigenspace for every `λ ≠ 0`: `−6m` on `λ = −m`, `−3m` on `λ = −2m`, `2m` on `λ = 3m`.

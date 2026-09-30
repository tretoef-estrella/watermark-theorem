# The Double Ladder Theorem, piece DL2: the rank of the Gram matrix modulo m

This is the second piece of the Lean 4 formalization of *The Double Ladder Theorem*. The Watermark Theorem (`RequestProject/Watermark/Defs.lean`, `W1.lean` … `W7.lean`, namespace `Watermark`) and piece DL1 (`RequestProject/DoubleLadder/DL1.lean`, namespace `DoubleLadder`) are already in this project. **Reuse their definitions and results unchanged, and do not edit those files.** Put this piece in `RequestProject/DoubleLadder/DL2.lean`, namespace `DoubleLadder`.

## Where this piece sits

For a prime `m ≥ 7`, `V*/V ≅ (ℤ/m)^{3m²−24m+59} × (ℤ/m²)^{3m−16}`. The proof has three inputs:
1. the order `m^{3(m−3)²}` (W7, done);
2. the exponent divides `m²` (DL1, done);
3. **`rank(G mod m) = 12(m − 3)` (this piece)**.

A later piece assembles them with the Smith normal form.

## Setting

From W1: `Point m = ZMod m × ZMod m`, `Line m = Fin 3 × Point m`, `gram m` (the matrix `G`), `V m`, `formV m`. From DL1: `DL1.projMat b`, `DL1.gram_eq_projMat : gram m = (projMat b)ᵀ * toMatrix b (formV m) * projMat b`, `DL1.exists_projMat_mul_eq_one`.

## Definitions

The four pencils used here, on a point `p = (k, l)`:

```
def pen4 {m : ℕ} : Fin 4 → Point m → ZMod m
  | 0 => fun p => p.1
  | 1 => fun p => p.2
  | 2 => fun p => p.1 - p.2
  | 3 => fun p => p.1 + p.2
```

Slots are `Slot m := Fin 3 × Fin 4 × ZMod m`: one slot for each family `j`, each of its four pencils `i`, and each value `x`.

**The shadow matrix.** `shadow m : Matrix (Slot m) (Line m) ℤ`, with
`shadow m (j, i, x) (j′, p) = if j′ = j ∧ pen4 i p = x then 1 else 0`.
Row `(j, i, x)` is the indicator of the fibre `{pen4 i = x}` of family `j`.

**The pairing matrix.** `gam m : Matrix (Slot m) (Slot m) ℤ`, where `gam m (j, i, x) (j′, i′, y) = 1` in exactly these cases, and `0` otherwise:
- `j = j′`, `i = i′ ∈ {0, 1}`, `x = y` (the axis slots, paired with themselves);
- `{(j, i), (j′, i′)} = {(0, 2), (1, 2)}` and `x = y`;
- `{(j, i), (j′, i′)} = {(1, 3), (2, 3)}` and `x = y`;
- `(j, i, j′, i′) = (0, 3, 2, 2)` and `y = x + 1`;
- `(j, i, j′, i′) = (2, 2, 0, 3)` and `x = y + 1`.

`gam m` is symmetric and `gam m * gam m = 1`.

**The one-family relation map.** Over `F := ZMod m`:
`relMap m : (Fin 4 → ZMod m → F) →ₗ[F] (Point m → F)`, `relMap m h p = Σ_i h i (pen4 i p)`.

**The six relations** (as `Fin 4 → ZMod m → F`, listed as `(h 0, h 1, h 2, h 3)`):
1. `(1, −1, 0, 0)`
2. `(1, 0, −1, 0)`
3. `(1, 0, 0, −1)` (all three constant)
4. `(x, −x, −x, 0)`
5. `(x, x, 0, −x)`
6. `(−2x², −2x², x², x²)` (the polarization identity `(k+l)² + (k−l)² = 2k² + 2l²`)

## Statements

**(DL2.a) The shadow factorization.** For every `m` with `[NeZero m]`:
`gram m = (shadow m)ᵀ * gam m * shadow m − (m : ℤ) • 1`.

**(DL2.b) The relations of one family.** For `m` prime with `5 ≤ m`: `LinearMap.ker (relMap m)` is the span of the six relations, and `Module.finrank (ZMod m) (LinearMap.ker (relMap m)) = 6`.

**(DL2.c) Quadratic pairings vanish.** For `m` prime with `7 ≤ m`, for `f, g : ZMod m → ZMod m` of the form `x ↦ a + b x + c x²` and every `e : ZMod m`:
`Σ_x f x * g (x + e) = 0`.

**(DL2.main) The rank.** For `m` prime with `7 ≤ m`:
`((gram m).map (Int.castRingHom (ZMod m))).rank = 12 * (m − 3)`.

**(DL2.basis) The rank in any basis.** For `m` prime with `7 ≤ m` and every `ℤ`-basis `b : Module.Basis ι ℤ (V m)` (`Fintype ι`, `DecidableEq ι`):
`((LinearMap.BilinForm.toMatrix b (formV m)).map (Int.castRingHom (ZMod m))).rank = 12 * (m − 3)`.

**(DL2.five) (welcome)** For `m = 5` the rank is `26`.

## Proof

Write `S̄`, `Γ̄`, `Ḡ` for the reductions mod `m`, over `F = ZMod m`.

### (DL2.a)
Compute the entry `(Sᵀ Γ S)(p, q) = Σ_{s, s′} S(s, p) Γ(s, s′) S(s′, q)` for lines `p = (j, a)` and `q = (j′, b)`. The four slots of `p` are `(j, i, pen4 i a)`.
- **Same family** (`j = j′`): only the axis self-pairs contribute, giving `[a.1 = b.1] + [a.2 = b.2]`. This is `2` on the diagonal (`= (2 − m) + m`) and, off the diagonal, `1` iff `p` and `q` share `k` or `l`. That is `gramUpper` for equal families.
- **Families 0 and 1:** only the pair `(0, 2) ↔ (1, 2)` contributes, giving `[a.1 − a.2 = b.1 − b.2]`.
- **Families 1 and 2:** only `(1, 3) ↔ (2, 3)`, giving `[a.1 + a.2 = b.1 + b.2]`.
- **Families 0 and 2:** only `(0, 3) ↔ (2, 2)` with the shift, giving `[b.1 − b.2 = a.1 + a.2 + 1]`.

These are exactly the cases of `gramUpper`. The case `j > j′` follows by symmetry (`gram_transpose`, `gam` symmetric). This is the Watermark row table (W3/W4); compare `gramUpper` in `Defs.lean`.

### (DL2.b)
*The relations lie in the kernel.*
- Relations 1–3: `1 − 1 = 0`.
- Relation 4: `k − l − (k − l) = 0`.
- Relation 5: `k + l − (k + l) = 0`.
- Relation 6: `−2k² − 2l² + (k − l)² + (k + l)² = 0`.

*They are independent.* Evaluate at `x = 0, 1, 2`: the constant parts, the linear parts and the quadratic part separate, using `2 ≠ 0` and `m ≥ 5`.

*The kernel is contained in their span* (the finite-difference argument of W2's Lemma C). Let `h ∈ ker relMap` and `Φ(k, l) := h₀(k) + h₁(l) + h₂(k − l) + h₃(k + l) = 0`.
1. Take the mixed difference `Φ(k+1, l+1) − Φ(k+1, l) − Φ(k, l+1) + Φ(k, l) = 0`. The terms `h₀` and `h₁` cancel, and
   `h₃(s + 2) − 2h₃(s + 1) + h₃(s) = h₂(t + 1) − 2h₂(t) + h₂(t − 1)`, with `s = k + l`, `t = k − l`.
2. Since `2` is invertible (`m` odd), `(k, l) ↦ (k + l, k − l)` is a bijection of `Point m`. So the left side depends only on `s`, the right side only on `t`, and both equal one constant `c`.
3. A function `ZMod m → F` whose second difference is the constant `c` is `x ↦ β + α x + (c/2) x²` (as in W2's Lemma C; `m` odd). So `h₂` and `h₃` are quadratics with the same leading coefficient `c/2`.
4. Then `h₀(k) + h₁(l) = −h₂(k − l) − h₃(k + l)`, whose `kl`-terms cancel. Setting `l = 0`, then `k = 0`, shows that `h₀` and `h₁` are quadratics.
5. Matching coefficients writes `h` as a combination of the six relations.

Hence `ker relMap = span`, and `finrank = 6`.

### (DL2.c)
`f(x) g(x + e)` is a polynomial in `x` of degree `≤ 4` with coefficients in `F`. By `FiniteField.sum_pow_lt_card_sub_one`, `Σ_{x ∈ ZMod m} x^s = 0` for `s < m − 1`, and `4 < m − 1` when `m ≥ 7`.

### (DL2.main)
Over `F`, `Ḡ = S̄ᵀ Γ̄ S̄` by (DL2.a). Put `n = 3m²`, `U = Slot m → F` (dimension `12m`), `R := ker(S̄ᵀ) ⊆ U`.
1. **`R` family by family.** `S̄ᵀ` acts separately on the three families: its restriction to the slots of family `j` is `relMap` placed on family `j`. So `R = ⊕_j` (a copy of `ker relMap`), and `finrank R = 18` by (DL2.b).
2. **`rank S̄ = 12m − 18`** (rank–nullity for `S̄ᵀ : U → F^n`, and `rank S̄ = rank S̄ᵀ`).
3. **`range S̄ = R^⊥`** for the dot product on `U`. The inclusion `⊆`: `(S̄x) ⬝ᵥ r = x ⬝ᵥ (S̄ᵀ r) = 0`. Equality holds by dimension, `12m − 18 = 12m − finrank R`.
4. **`Γ̄ R ⊆ range S̄`.** For `r, r′ ∈ R`, `(Γ̄ r) ⬝ᵥ r′` is a sum of pairings `Σ_x r_s(x) r′_{s′}(x + e)` of slot functions. By step 1 and (DL2.b), each slot function of an element of `R` is a quadratic, so every such pairing is `0` by (DL2.c). By step 3, `Γ̄ r ∈ range S̄`.
5. **The kernel of `Ḡ`.** `Ḡ x = 0 ⟺ S̄ᵀ(Γ̄ S̄ x) = 0 ⟺ Γ̄ S̄ x ∈ R ⟺ S̄ x ∈ Γ̄ R`, using `Γ̄² = 1`. By step 4, `Γ̄ R ⊆ range S̄`, so `ker Ḡ = S̄⁻¹(Γ̄ R)` has dimension `dim ker S̄ + dim Γ̄R = (n − (12m − 18)) + 18`.
6. **Conclusion.** `rank Ḡ = n − dim ker Ḡ = 12m − 36 = 12(m − 3)`.

### (DL2.basis)
By `DL1.gram_eq_projMat`, `G = Pᵀ M P`, and by `DL1.exists_projMat_mul_eq_one`, `P Q = 1`. Reducing mod `m`: `Ḡ = P̄ᵀ M̄ P̄` and `M̄ = Q̄ᵀ Ḡ Q̄`. So `rank Ḡ ≤ rank M̄ ≤ rank Ḡ` (`Matrix.rank_mul_le_left/right`). Use `Matrix.map_mul` and `Matrix.transpose_map`.

### (DL2.five)
At `m = 5`, (DL2.c) fails because `Σ_{x ∈ 𝔽₅} x⁴ = −1`. The `18 × 18` matrix of `Γ̄`-pairings between the eighteen relations has rank `2`. So `dim(range S̄ ∩ Γ̄R) = 16`, `dim ker Ḡ = (75 − 42) + 16 = 49`, and `rank Ḡ = 75 − 49 = 26`. Optional.

## Checks (run before sending)

All of the following hold at `m = 5, 7, 11, 13`, with the definitions exactly as above (`checks/dl2_checks.py`):
- (DL2.a) holds as an identity of integer matrices; `gam` is symmetric and `gam² = 1`.
- `dim ker relMap = 6`; the six relations lie in it and have rank 6.
- (DL2.c) holds at `m = 7, 11, 13` for every pair of monomials `xⁱ, xʲ` (`i, j ≤ 2`) and every shift `e ∈ {0, ±1}`. At `m = 5` three pairings are nonzero (control).
- `rank(Ḡ) = 48, 96, 120` at `m = 7, 11, 13`, which is `12(m − 3)`; and `26` at `m = 5`.
- The intermediate dimensions of the proof: `dim range S̄ = 12m − 18`; `dim(range S̄ ∩ Γ̄R) = 18` for `m = 7, 11, 13` and `16` for `m = 5` (`checks/dl_steps.py`).

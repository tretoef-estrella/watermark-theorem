# The Double Ladder Theorem, piece DL3: the assembly (the final theorem)

This is the third and last piece of the Lean 4 formalization of *The Double Ladder Theorem*. The following are already in this project:
- the Watermark Theorem: `RequestProject/Watermark/Defs.lean`, `W1.lean` … `W7.lean`, namespace `Watermark`;
- pieces DL1 and DL2: `RequestProject/DoubleLadder/DL1.lean`, `DL2.lean`, namespace `DoubleLadder`.

**Reuse their definitions and results unchanged, and do not edit those files.** Put this piece in `RequestProject/DoubleLadder/DL3.lean`, namespace `DoubleLadder`.

## The target

> **Theorem (The Double Ladder).** For every prime `m ≥ 7`, the discriminant group of the lattice `V` of the lines on the Fermat surface of degree `m` is
> `V*/V ≅ (ℤ/m)^{3m²−24m+59} × (ℤ/m²)^{3m−16}`.
> For `m = 5` it is `(ℤ/5)^{10} × ℤ/25`.

In Lean the discriminant group is

`D m := Module.Dual ℤ (V m) ⧸ LinearMap.range (formV m)`.

Here `formV m : V m →ₗ[ℤ] V m →ₗ[ℤ] ℤ` is a linear map `V m →ₗ[ℤ] Module.Dual ℤ (V m)`, so `v ↦ formV m v` is the canonical map `V → V*`.

## Statements

**(DL3.main)** For `m` prime with `7 ≤ m`:
`Nonempty (D m ≃+ ((Fin (3 * m ^ 2 + 59 - 24 * m) → ZMod m) × (Fin (3 * m - 16) → ZMod (m ^ 2))))`.

The exponent is written `3 * m ^ 2 + 59 - 24 * m` on purpose: in `ℕ`, `3 * m ^ 2 - 24 * m + 59` would truncate at `m = 7`.

**(DL3.five)** `Nonempty (D 5 ≃+ ((Fin 10 → ZMod 5) × ZMod 25))`.

**(DL3.group) (welcome, and the heart of the assembly)** Let `p` be a prime and `H` a finite additive commutative group with:
- `p² • x = 0` for all `x`;
- `Nat.card H = p ^ N`;
- `Nat.card (H ⧸ (p • ⊤ : AddSubgroup H)) = p ^ c` (equivalently, `H ⧸ pH` has `p^c` elements).

Then `2c ≥ N ≥ c`, and `Nonempty (H ≃+ ((Fin (2c − N) → ZMod p) × (Fin (N − c) → ZMod (p ^ 2))))`.

## Available results

- **W7** `watermark_theorem hm`: `V m` is free, `finrank = 3(m−1)(m−2)+1`, and `det (toMatrix b (formV m)) = m^(3(m−3)²)` for every basis `b`.
- **DL1:**
  - `exists_formV_eq_smul hm f : ∃ v, ((m:ℤ)^2) • f = formV m v`, i.e. `m² · D = 0`;
  - `exists_toMatrix_mul_eq`.
- **DL2:**
  - `rank_toMatrix_map hm b : ((toMatrix b (formV m)).map (Int.castRingHom (ZMod m))).rank = 12 * (m − 3)` for `m ≥ 7`;
  - `rank_gram_map_five`: at `m = 5` the rank of `gram 5` mod 5 is `26`, which transfers to any basis exactly as in (DL2.basis).
- **DL1 helpers:** `DL1.gram_eq_projMat`, `DL1.exists_projMat_mul_eq_one`.

## Proof

Fix a basis `b : Module.Basis ι ℤ (V m)` (for instance `Module.Free.chooseBasis`), and let `M := toMatrix b (formV m)`, an integer symmetric matrix of size `r = 3(m−1)(m−2)+1`.

**Step 1. `D m ≅ ℤ^ι ⧸ range M`.** The map `Module.Dual ℤ (V m) → (ι → ℤ)`, `f ↦ (f (b i))_i`, is an isomorphism. It carries `formV m v` to `(formV m v (b i))_i = M *ᵥ c`, where `c = b.repr v`, using the symmetry `formV_isSymm`. So it induces `D m ≃+ (ι → ℤ) ⧸ LinearMap.range M.mulVecLin`.

**Step 2. Order.** `Nat.card ((ι → ℤ) ⧸ range M) = |det M| = m^{3(m−3)²}`, by W7. Mathlib: the index of the range of an injective integer matrix equals `|det|` (`Submodule.natAbs_det_basis_change`, as used in W6/W7, or `Int.natAbs_det_eq_…`/`AddSubgroup.index` of `range`). In particular `D m` is finite. Set `N = 3(m−3)²`.

**Step 3. Exponent.** `m² • D m = 0` by DL1 (`exists_formV_eq_smul`).

**Step 4. The quotient by m.** `D/mD ≅ (ι → ℤ) ⧸ (range M + m·ℤ^ι) ≅ (ι → ZMod m) ⧸ range M̄`, where `M̄ = M.map (Int.castRingHom (ZMod m))`. So `Nat.card (D/mD) = m^{r − rank M̄}`. By DL2, `rank M̄ = 12(m − 3)` for `m ≥ 7` (and `26` for `m = 5`). Hence `c := r − rank M̄ = 3m² − 21m + 43` (and `11` for `m = 5`).

**Step 5. (DL3.group).** By the structure theorem (`AddCommGroup.equiv_directSum_zmod_of_finite`, or `equiv_directSum_zmod_of_finite'`), `H ≃+ ⊕_k ZMod (q_k^{e_k})` with `q_k` prime and `e_k ≥ 1`. Since `p² H = 0`, every `q_k = p` and `e_k ∈ {1, 2}`. With `a := #{e_k = 1}` and `b := #{e_k = 2}`:
- `|H| = p^{a + 2b}`;
- `|H/pH| = p^{a + b}`, since `ZMod (p^e) ⧸ p·ZMod (p^e) ≅ ZMod p` for `e ≥ 1`.

So `a + 2b = N` and `a + b = c`, hence `a = 2c − N` and `b = N − c`. Regroup the direct sum into `(Fin a → ZMod p) × (Fin b → ZMod (p²))`.

**Step 6. Arithmetic.**
- `N = 3(m−3)² = 3m² − 18m + 27` and `c = 3m² − 21m + 43`, so `2c − N = 3m² − 24m + 59` and `N − c = 3m − 16`.
- For `m = 5`: `N = 12`, `c = 11`, so `a = 10` and `b = 1`.

For `m ≥ 7` all quantities are positive, and `3m² + 59 ≥ 24m`.

## Checks (run before sending)

- The elementary-divisor profiles of `G` over `ℤ_{(m)}` (`checks/dl_profile.log`):
  - `m = 5`: `{0: 26, 1: 10, 2: 1}`;
  - `m = 7`: `{0: 48, 1: 38, 2: 5}`;
  - `m = 11`: `{0: 96, 1: 158, 2: 17}`;
  - `m = 13`: `{0: 120, 1: 254, 2: 23}`;

  in every case, plus `9m − 7` zeros for the kernel.
- `a = 2c − N` and `b = N − c`, with `c = r − 12(m−3)` and `N = 3(m−3)²`, give `(38, 5)`, `(158, 17)` and `(254, 23)` at `m = 7, 11, 13`, and `(10, 1)` at `m = 5` with `c = 11`. These match the profiles.
- The three anchors of the June paper, AMV `m = 5, 7` and the sealed `m = 11`, and the new cell `m = 13`.

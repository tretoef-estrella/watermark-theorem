# The Watermark Theorem, piece W4: pullbacks along pencils and how the Gram matrix acts on them

Fourth piece of the Lean 4 formalization of *The Watermark Theorem*. Pieces W1–W3 are in this project (`RequestProject/Watermark/Defs.lean`, `W1.lean`, `W2.lean`, `W3.lean`, namespace `Watermark`). **Reuse their definitions unchanged and do not edit those files.** Put this piece in `RequestProject/Watermark/W4.lean`.

Later pieces will prove `mK ⊆ SAT`, compute an index and a discriminant, and assemble `|disc V| = m^{3(m−3)²}`; they all use the identities below.

## Setting

From W1: `Point m = ZMod m × ZMod m`, `Line m = Fin 3 × Point m`, `gram m` (the matrix `G`), `A m = Line m → ℤ`, `famVec`, `pencil : Option (ZMod m) → Point m → ZMod m` (`some t ↦ (k, l) ↦ k + t·l`, `none ↦ (k, l) ↦ l`), `sumZero ℤ m` (W2).

Throughout, `m` is prime and `m ≥ 5` (weaker hypotheses are welcome where the proof allows). For `t ∈ ZMod m`, «pencil `t`» means `pencil (some t)`; so pencil `1` is `k + l` and pencil `−1` is `k − l`.

**Pullback.** For `j ∈ Fin 3`, `π : Option (ZMod m)` and `u : ZMod m → ℤ`, let `pb j π u : A m` be

`pb j π u (j′, k, l) := if j′ = j then u(pencil π (k, l)) else 0`.

**Fibre sums.** For `π` and `y : Point m → ℤ`, let `fib π y : ZMod m → ℤ`, `fib π y (v) := Σ_{p : pencil π p = v} y(p)`.

## Statements

**(W4.a) Two pencils are independent coordinates.** For `π ≠ π′` and all `u, v : ZMod m → ℤ`:
`Σ_{p ∈ Point m} u(pencil π p) · v(pencil π′ p) = (Σ_x u(x)) · (Σ_x v(x))`;
and for one pencil: `Σ_{p} u(pencil π p) · v(pencil π p) = m · Σ_x u(x) v(x)`.

**(W4.b) The Gram matrix on pullbacks of sum-zero functions.** Let `u ∈ sumZero ℤ m`.

1. *Axis pencils:* `gram m *ᵥ pb j (some 0) u = 0` and `gram m *ᵥ pb j none u = 0`, for every `j`.
2. *Live non-overlap pencils:* for `t ∉ {0, 1, −1}`, `gram m *ᵥ pb j (some t) u = −m • pb j (some t) u`, for every `j`.
3. *Overlap pencils.* With `u⁺(x) := u(x + 1)` and `u⁻(x) := u(x − 1)`:
   - `G · pb 0 (−1) u = −m • pb 0 (−1) u + m • pb 1 (−1) u`
   - `G · pb 1 (−1) u = −m • pb 1 (−1) u + m • pb 0 (−1) u`
   - `G · pb 1 (1) u = −m • pb 1 (1) u + m • pb 2 (1) u`
   - `G · pb 2 (1) u = −m • pb 2 (1) u + m • pb 1 (1) u`
   - `G · pb 0 (1) u = −m • pb 0 (1) u + m • pb 2 (−1) u⁻`
   - `G · pb 2 (−1) u = −m • pb 2 (−1) u + m • pb 0 (1) u⁺`

   (Here `pb j (t) u` abbreviates `pb j (some t) u`, and `G · x` is `gram m *ᵥ x`.)

**(W4.c) Fibre decomposition of one family (R.1 as a vector identity).** For every `y : Point m → ℤ` and every `j`, writing `ext j y : A m` for `y` placed on family `j` (zero elsewhere):
`m • ext j y = Σ_{π : Option (ZMod m)} pb j π (fib π y) − (Σ_p y(p)) • famVec m j`.

## Proofs

**(W4.a)** For `π ≠ π′` the map `p ↦ (pencil π p, pencil π′ p)` is a bijection `Point m → ZMod m × ZMod m` (two distinct pencils are two independent linear forms on `(ZMod m)²`, `m` prime), so the sum is `Σ_{x, y} u(x)v(y)`. For one pencil, each fibre has exactly `m` points.

**The row of G** (as in W3). For a line `p = (j, k, l)` the row of `G` has `2 − m` at `p`, `1` at `(j, k, l′)` (`l′ ≠ l`) and at `(j, k′, l)` (`k′ ≠ k`), and, in each other family `j′`, `1` on an incidence set `S_{j′}(p)`:
- `p` in family 0: `S_1 = {k′ − l′ = k − l}`, `S_2 = {k′ − l′ = k + l + 1}`;
- `p` in family 1: `S_0 = {k′ − l′ = k − l}`, `S_2 = {k′ + l′ = k + l}`;
- `p` in family 2: `S_0 = {k′ + l′ = k − l − 1}`, `S_1 = {k′ + l′ = k + l}`.

So a line of another family sees family `j` through one set of the form `{k′ − l′ = c}` and one of the form `{k′ + l′ = c}`.

**(W4.b)** Let `v = pb j π u`.
- *Same family* (the entries of `G v` on family `j`). If `π = none` (value `u(l′)`): `(2 − m)u(l) + (m − 1)u(l) + Σ_{l′ ≠ l} u(l′) = Σ u = 0`; same for `π = some 0`. If `π = some t` with `t ≠ 0`: the row `k′ = k` and the column `l′ = l` each meet every fibre of the pencil exactly once (`t` is invertible), so the entry is `(2 − m)u(x) + 2(Σu − u(x)) = −m·u(x)`, `x = pencil π (k, l)`.
- *Other families.* The entry is `Σ_{(k′, l′) ∈ S} u(pencil π (k′, l′))` over an incidence set `S`. On `{k′ − l′ = c}` the pencil `t` takes the values `(1 + t)k′ − tc`, a bijection onto `ZMod m` unless `t = −1`; the axis pencils `k′` and `l′` are bijections too. On `{k′ + l′ = c}` the pencil `t` is `(1 − t)k′ + tc`, a bijection unless `t = 1`. A bijection gives `Σ u = 0`. When the pencil is constant on `S` (`t = −1` on a `−` set, `t = 1` on a `+` set) the entry is `m·u(value)`, and reading off the value from the table gives the six overlap formulas; for instance at `(2, k, l)` for `v = pb 0 (1) u` the set is `{k′ + l′ = k − l − 1}`, where `k′ + l′ = k − l − 1`, so the entry is `m·u(k − l − 1) = m·u⁻(k − l)`.

**(W4.c)** This is W1's `sum_E_pencil` (paper R.1) applied at each point of family `j`: `(E_π y)(p) = fib π y (pencil π p)`, so `Σ_π pb j π (fib π y)` at `(j, p)` is `m·y(p) + Σ_q y(q)`; off family `j` both sides vanish.

## Checks (run before sending)

- `m = 5, 7, 11`: every formula of (W4.b) holds on the whole basis `δ_x − δ_0` of `sumZero ℤ m`, for every family and every pencil. The two `(0,2)` formulas hold only with the shifts written (`u⁻` in the first, `u⁺` in the second); every other shift fails (control).
- The route these identities serve was checked end to end at `m = 5`: the index `[ℤ^{Point m} : Σ_π pb^π(Z₀) + ℤ·𝟙] = 5^16` (also `7^29`, `11^67`, the predicted `m^{(m²+m+2)/2}`), and the final value `|disc V| = 5^{12}`.

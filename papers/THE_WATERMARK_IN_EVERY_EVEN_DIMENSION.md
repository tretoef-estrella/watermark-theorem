# THE WATERMARK IN EVERY EVEN DIMENSION
## The discriminant of the Hodge lattice of a Fermat variety of prime degree

**Rafael Amichis Luengo**

Madrid, Spain · tretoef@gmail.com · 1 October 2026 · version 2

A sequel to *The Watermark and Double Ladder Theorems* [WDL] and to *The Chaise Longue Theorem*, version 10 [CL]. Version 1 of this note stated the main formula as a conjecture and was not released; in this version it is a theorem.

---
## Summary

For the Fermat surface of prime degree `p`, Shioda asked in 1987 whether the determinant of the Néron–Severi lattice is `p^{3(p−3)^2}` [Shi87]. It is (the *Watermark* theorem [WDL], verified in Lean). This note gives the answer **in every even dimension**.

Let `X ⊂ P^{2k+1}` be the Fermat variety of degree `m` and dimension `2k`, let `G = μ_m^{2k+2}/μ_m` be its group of diagonal automorphisms, and let `Hdg(X)` be the lattice of integral Hodge classes of middle degree.

1. **The discriminant group is a finite ring (Theorem 1, every degree `m ≥ 3`).** `Hdg(X)^∨/Hdg(X) ≅ Z[G]/(I_𝔅 + I_T)`, where `I_𝔅` and `I_T` are the ideals of the elements of the group ring that vanish at the Hodge characters and at the remaining primitive characters. In words: the discriminant group is the coordinate ring of the intersection, inside `Spec Z[G]`, of the Hodge locus with its complement.
2. **The exponent is a delta invariant (Theorem 2, `m = p` prime).** `|disc Hdg(X)| = p^E` with `E = 1 + (2k(p−2) − 1)·B − 2δ_𝔅`. Here `B` is the number of Hodge characters up to scalars and `δ_𝔅` is the delta invariant of the order `Z_p[G]/I_𝔅`, an arithmetic curve with `B` branches through one point.
3. **The formula (Theorem 3).** The tangent cone of that curve is the cone over the Hodge points `[𝔅] ⊂ P^{2k}(F_p)`, and its coordinate ring modulo `x_0^{p−1}` is the ring of Theorem A of [CL] with the even box `p − 1`. Hence **`E_k(p) = 1 + (2k(p−2) − 1)·B − 2·Σ_i ⌊i/(p−1)⌋·a(i)`**, with `a` the Hilbert function of `F_p[x_0, …, x_{2k+1}]/(e_1, e_3, …, e_{2k+1}; x_i^{p−1})`. This step uses one count, the dimension of that ring, which follows from a theorem of Bezrukavnikov, Riche and Rider [BRR] as explained in [CL, Note]. Without it, the right-hand side is still a **lower bound** for `E_k(p)`; and in the 22 cells where the count was checked by machine the formula does not depend on [BRR].
4. **Closed forms.** For the Fermat cubic of dimension `2k`: `|disc Hdg(X)| = 3^{2·4^k + 1 − 3·C(2k+1, k)}`. For the lattice spanned by the `p^{k+1}` linear spaces of one matching: discriminant `p^{1 + (p−1)^k·(k(p−2) − 1)}` (Theorem 4, with no use of [BRR]). For surfaces the formula returns `3(p−3)^2`.
5. **Verification.** The formula agrees with every published computation for prime degree known to us: ten cells `(dimension, degree)`. For nine of them the tables of Aljovin, Movasati and Villaflor [AMV] give the lattice or its primitive part; `(4, 7)` is new, and so is the lattice of linear cycles at `(6, 3)`. (For surfaces, the determinant had also been checked by computer for odd degrees up to `81` [SSvL].) Each identity used in the proof was checked by a separate engine that computes the orders directly in the group ring; that engine also confirms two cells for which no lattice computation exists, `(6, 5)` and `(12, 3)`. Theorem 1 and its variant for the linear cycles (Remark (ii) of §2) were tested at composite degrees too: five cells against [AMV], with all the elementary divisors, and the Fermat sextic surface against [ABB].

**What the proof rests on.** Pham's theorem on the homology of the affine Fermat variety, in the form given by Looijenga [Loo, Corollary 2.2]; the Hodge type of the eigenspaces [SK] and Shioda's description of the Hodge characters for prime degree [Shi79], [Ran]; for Theorem 4, [DS, Corollary 1.6]; and, for Theorem 3 in general, [BRR, Proposition 2.12].

**What is open.** Two conjectures: that `E_k(p)` is a polynomial in `p` of degree `k + 1` (for `k ≤ 7` we give it; it agrees with every value computed, at primes up to `43`); and that the transcendental side, too, is governed by its tangent cone, so that `E_k(p)` is the length of the intersection of two cones over points of `P^{2k}(F_p)`. And three problems: the elementary divisors of the discriminant group, composite degrees, a proof without [BRR] (§9).

**Status.** Nothing here is refereed. The proofs were read cold by an independent reader before release; its findings are incorporated (§10).

---
## 1. Setting and notation

Throughout, `k ≥ 1`, `n = 2k`, `N = 2k + 2`, `m ≥ 3`, and `X = X^m_{2k} ⊂ P^{2k+1}` is the Fermat variety `z_0^m + … + z_{N−1}^m = 0`. From §4 on, `m = p` is an odd prime.

**1.1 Lattices.** `H := H_n(X, Z)` with the intersection form is unimodular. `η ∈ H` is the class of a linear section of dimension `k`; `η·η = m`. `H° := η^⊥` is the primitive homology. `Hdg(X) ⊂ H` is the lattice of integral Hodge classes; it is primitive, it contains `η`, and the form is non-degenerate on it. `T(X) := Hdg(X)^⊥` is the transcendental lattice; `T(X) ⊂ H°`. Put `Hdg° := Hdg(X) ∩ H°`. `L(X) ⊂ Hdg(X)` is the sublattice generated by the classes of the `(2k+1)!!·m^{k+1}` standard linear `k`-spaces of `X`; a standard space `P` has `P·η = 1`.

- For `m` odd, `L(X)` is primitive in `H` (Conjecture 1.2 of Degtyarev and Shimada [DS], proved in [CL, Main Theorem]).
- For `m = p` prime, `Hdg(X) = L(X)`, of rank `Q_k(p) + 1` [CL, Corollary H]. This fact is not used below; only the description of the Hodge characters in 1.2 is. Here `Q_k(p)` is the number of vectors of `(F_p ∖ 0)^N` whose coordinates can be matched in pairs `{a, −a}`; it is the number of closed walks of length `N` on `Z^{(p−1)/2}` with steps `±ε_i`.

**1.2 Characters.** `G := μ_m^N/μ_m` acts on `X`. Let `u_0, …, u_{N−1} ∈ G` be the images of the generators of the factors; `u_0·u_1⋯u_{N−1} = 1`. The characters of `G` are the vectors `a = (a_0, …, a_{N−1}) ∈ (Z/m)^N` with `Σ a_ν = 0`: `χ_a(u_ν) = ζ^{a_ν}`, `ζ = e^{2πi/m}`. Write

- `𝔄` for the characters with no zero coordinate (the *primitive* characters);
- `𝔅 ⊂ 𝔄` for the *Hodge* characters: those `a` with `Σ_ν {t·a_ν/m} = k + 1` for every unit `t` of `Z/m` [SK], [Shi79];
- `T := 𝔄 ∖ 𝔅`.

For `m = p` prime, `𝔅` is the set of the `a ∈ 𝔄` whose coordinates can be matched in pairs `{a_i, a_j}` with `a_i + a_j = 0` [Shi79], [Ran]; `|𝔅| = Q_k(p)`.

For a set `Y` of characters, `I_Y := {x ∈ Z[G] : χ_a(x) = 0 for every a ∈ Y}`, an ideal of `Z[G]`.

**1.3 Pham's theorem, after Looijenga.** For a `G`-lattice `M` with an invariant form, put `a ⋆ b := Σ_{g ∈ G} (a·gb)·g ∈ Z[G]`, so that `a·b` is the coefficient of `1` in `a ⋆ b`.

> **Theorem (Pham [Ph]; Looijenga [Loo, Proposition 2.1 and Corollary 2.2]).** `H°` is a cyclic `Z[G]`-module, generated by the image `e` of the Pham cycle, and the intersection form is `(−1)^{n(n+1)/2}⋆` with
> `e ⋆ e = θ := Π_{ν=0}^{N−1} (1 − u_ν) ∈ Z[G]`.

So for `x, y ∈ Z[G]`: `(xe)·(ye) = ± ε(x·ȳ·θ)`, where `ε` is the coefficient of `1` and `ȳ` is the image of `y` under `g ↦ g^{−1}`. Since `χ_a(θ) = Π_ν (1 − ζ^{a_ν})` is non-zero exactly for `a ∈ 𝔄`, and the form is non-degenerate on `H°`, the annihilator of `e` is `I_𝔄`:

> `H° ≅ Z[G]/I_𝔄`, `x·e ↤ x`.

Under this isomorphism, `H° ⊗ C` is the sum of the eigenlines of the characters in `𝔄`, and the eigenline of `a` has Hodge type `(k, k)` exactly when `Σ_ν {a_ν/m} = k + 1` [SK]. We claim

> `Hdg° = I_T·e` and `T(X) = I_𝔅·e`. (1)

*Proof.* A class `x·e ∈ H°` is rational, so the set of the characters `a` with `χ_a(x) ≠ 0` is stable under `a ↦ ta`, `t ∈ (Z/m)^*`. Hence `x·e` is a Hodge class if and only if that set consists of characters all of whose multiples `ta` have type `(k, k)`, that is, lies in `𝔅`; that is, `x ∈ I_T` (modulo `I_𝔄`). For the second equality: `y·e` is orthogonal to `I_T·e` if and only if `ε(x·ȳ·θ) = 0` for every `x ∈ I_T`; since `I_T` is an ideal, this means `x·ȳ·θ = 0` for every `x ∈ I_T`, that is, `χ_a(x)·χ_{−a}(y)·χ_a(θ) = 0` for every `a`. For `a ∈ 𝔅` there is an `x ∈ I_T` with `χ_a(x) ≠ 0` (for instance `|G|` times the sum of the idempotents of the multiples `ta` of `a`), and `χ_a(θ) ≠ 0`; so the condition is `χ_a(y) = 0` on `−𝔅 = 𝔅`. ∎

(Both `𝔅` and `T` are stable under `a ↦ −a` and under `a ↦ ta`, `t ∈ (Z/m)^*`, so (1) does not depend on the conventions that identify characters on homology and on cohomology.) For surfaces, (1) is [ABB, Proposition 2.10], where Looijenga's description is used to compute the transcendental lattice of the Fermat sextic.

---
## 2. The discriminant group is a finite ring

> **Theorem 1.** Let `m ≥ 3` and `n = 2k ≥ 2`. As `Z[G]`-modules,
> `Hdg(X)^∨/Hdg(X) ≅ Z[G]/(I_𝔅 + I_T)`.
> In particular `|disc Hdg(X)| = |disc T(X)| = |Z[G]/(I_𝔅 + I_T)|`.

*Proof.* (a) Since `H` is unimodular and `Hdg(X)` is primitive and non-degenerate, the map `H → Hdg(X)^∨`, `x ↦ (x·−)`, is surjective with kernel `T(X)`. So `Hdg(X)^∨/Hdg(X) ≅ H/(Hdg(X) ⊕ T(X))`, and the same holds for `T(X)`.

(b) The inclusion `H° ⊂ H` induces an injection `H°/(Hdg° ⊕ T(X)) → H/(Hdg(X) ⊕ T(X))`, because `H° ∩ (Hdg(X) ⊕ T(X)) = Hdg° ⊕ T(X)`. It is surjective: a standard space `P` lies in `Hdg(X)` and has `P·η = 1`, so every `x ∈ H` is `(x·η)·P` plus an element of `H°`; hence `H = Hdg(X) + H°`.

(c) By (1), `H°/(Hdg° ⊕ T(X)) = Z[G]e/(I_T e + I_𝔅 e) ≅ Z[G]/(I_T + I_𝔅)`, since `I_𝔄 ⊂ I_T ∩ I_𝔅`. All the maps are `G`-equivariant. ∎

**Remarks.** (i) The ring `𝒟 := Z[G]/(I_𝔅 + I_T)` is finite, because `𝔅` and `T` are disjoint. Its spectrum is the scheme-theoretic intersection of the closed subschemes `V(I_𝔅)` and `V(I_T)` of `Spec Z[G]`: of the Hodge characters and of the others. It is supported at the primes dividing `m`.

(ii) The same proof gives, for every `m ≥ 3`: if `𝔇 ⊂ 𝔄` is the set of the characters whose coordinates can be matched in pairs `{a_i, a_j}` with `a_i + a_j = 0` (for even `m` this allows `a_i = a_j = m/2`), then `Λ^∨/Λ ≅ Z[G]/(I_𝔇 + I_{𝔄∖𝔇})` for the saturation `Λ` of `L(X)` in `H`. What replaces (1) is that `Λ ∩ H° = I_{𝔄∖𝔇}·e`: the `m^{k+1}` standard spaces of a matching `J` form one orbit of `G`, with stabilizer `{g : g_i = g_j on the pairs of J}`, so the characters that occur in `L(X) ⊗ C` are trivial on one of these stabilizers, that is, they are `0` or lie in `𝔇`; and the rank of `L(X)` is `|𝔇| + 1` [DS, Theorem 1.4]. For `m` odd, `Λ = L(X)` by [CL, Main Theorem]; for surfaces of degree `m ≤ 4` or prime to `6` this is due to Degtyarev [Deg], and [DS, §5] verified it by computer for `(n, m) = (4, m)` with `3 ≤ m ≤ 12` and for `(6, 3), (6, 4), (6, 5), (8, 3)`.

(iii) We have not found Theorem 1 in the literature (nor did the cold reader of §10, who searched for it). The description (1) of the two lattices inside the group ring is known ([Loo]; [ABB, Proposition 2.10] for surfaces), and the proof of Theorem 1 is a few lines from there, so it may well be known to the specialists; if a reference exists, it should replace this paragraph.

**Check.** The group `Z[G]/(I_𝔅 + I_T)` was computed in ten cells (§8, engine 6, Table 4): it is `(Z/8)^2` for the Fermat quartic surface, `(Z/5)^{10} × Z/25` at `(2, 5)`, `Z/3 × Z/9` at `(4, 3)`, `(Z/3)^7 × (Z/9)^7 × Z/27` at `(6, 3)`. These are the discriminant groups of `Hdg(X)` in [AMV, Table 1] and in Table 1 below. For the Fermat sextic surface, where the lines do not generate the Néron–Severi lattice, it is `Z/4 × (Z/12)^9 × (Z/36)^9 × Z/108`, of order `2^{40}·3^{30}`: the discriminant of the transcendental lattice found in [ABB, Remark 3.5]. Remark (ii) was tested in the same way at `(2, 6), (2, 8), (2, 9), (2, 10)` and `(4, 4)`: in each cell the group is the one of [AMV, Table 1], with all its elementary divisors.

---
## 3. Orders, delta invariants and discriminants

From here on `m = p` is an odd prime, `ζ = e^{2πi/p}`, `π := ζ − 1`, and `r := N − 1 = 2k + 1`, so `|G| = p^r`.

**3.1 The orders.** Let `Y ⊂ 𝔄` be stable under multiplication by `F_p^*`, and `[Y]` its set of orbits (a set of points of the projective space of characters, `P^{2k}(F_p)`). Choose a representative `a` in each orbit and put

> `Õ_Y := Π_{[a] ∈ [Y]} Z[ζ]`, `A_Y :=` the image of `Z[G]` in `Õ_Y` under `x ↦ (χ_a(x))_a`.

So `A_Y ≅ Z[G]/I_Y`. The index of `A_Y` in `Õ_Y` is finite and a power of `p` (after inverting `p`, the group ring of the `p`-group `G` is a product of rings `Z[1/p][ζ]` and `Z[1/p]`). Define

> `δ_Y := log_p [Õ_Y : A_Y]`.

`Spec A_Y ⊗ Z_p` is a curve with `|[Y]|` branches, each a copy of `Spec Z_p[ζ]`, through one closed point, and `δ_Y` is its delta invariant. Write `α := |[𝔄]|`, `B := |[𝔅]| = Q_k(p)/(p−1)`, `t := |[T]| = α − B`.

**Lemma 3.2 (intersection number).** If `Y = Y_1 ⊔ Y_2`, then `log_p |Z[G]/(I_{Y_1} + I_{Y_2})| = δ_Y − δ_{Y_1} − δ_{Y_2}`.

*Proof.* `A_Y ⊂ A_{Y_1} × A_{Y_2} ⊂ Õ_{Y_1} × Õ_{Y_2} = Õ_Y`, and `(x, y) ↦ x − y` induces an isomorphism `(A_{Y_1} × A_{Y_2})/A_Y ≅ Z[G]/(I_{Y_1} + I_{Y_2})`. ∎

**Lemma 3.3 (discriminant of a lattice supported on `Y`).** Let `M ⊂ H°` be a sublattice of the form `M = 𝔪·e`, with `𝔪 ⊂ Z[G]` a subgroup whose elements vanish at every character of `𝔄 ∖ Y`, and `M` of rank `|Y|`. Let `M_Y ⊂ Õ_Y ⊗ Q` be the image of `𝔪`. Then

> `v_p(disc M) = −κ·|[Y]| + 2·log_p [Õ_Y : M_Y]`, with `κ := 2k(p−2) − 1`.

(For lattices `M_Y` not contained in `Õ_Y` the index is the generalized index.)

*Proof.* For `x, y ∈ 𝔪`, `(xe)·(ye) = ± ε(xȳθ) = ± p^{−r}·Σ_{a ∈ Y} χ_a(x)·χ_a(ȳ)·χ_a(θ) = ± p^{−r}·Tr(x·ȳ·θ)`, where `Tr` is the trace of the `Q`-algebra `K_Y := Õ_Y ⊗ Q` and `ȳ` is complex conjugation on each factor. So `disc M = ± p^{−r|Y|}·N_{K_Y/Q}(θ)·disc_{Tr}(M_Y)` (the conjugation changes the determinant by a sign). Now `|Y| = (p−1)·|[Y]|`; `disc_{Tr}(M_Y) = disc(Õ_Y)·[Õ_Y : M_Y]^2` and `disc Z[ζ] = ± p^{p−2}`; and `N_{Q(ζ)/Q}(1 − ζ^j) = p` gives `N_{K_Y/Q}(θ) = ± p^{N·|[Y]|}`. The exponent of `p` is `[−r(p−1) + (p−2) + N]·|[Y]| + 2·log_p[Õ_Y : M_Y]`, and `r(p−1) − (p−2) − N = 2k(p−2) − 1`. ∎

> **Theorem 2.** Let `p` be an odd prime, `k ≥ 1`, and `E := v_p(disc Hdg(X^p_{2k}))`. Then `|disc Hdg(X)| = p^E` and
> - (i) `2δ_𝔄 = 1 + κ·α`;
> - (ii) `E = 1 + κ·B − 2δ_𝔅`;
> - (iii) `E = κ·t − 2δ_T`;
> - (iv) `E = δ_𝔄 − δ_𝔅 − δ_T`.
>
> Here `κ = 2k(p−2) − 1`.

*Proof.* `|disc Hdg(X)|` is the order of `Z[G]/(I_𝔅 + I_T)` by Theorem 1, a power of `p`; and (iv) is Theorem 1 with Lemma 3.2.

(i) `|disc H°| = p`: `Zη ⊕ H°` has index `p` in the unimodular lattice `H`, and `η·η = p`. Apply Lemma 3.3 to `M = H°`, `𝔪 = Z[G]`, `Y = 𝔄`, `M_Y = A_𝔄`.

(ii) `Zη ⊕ Hdg°` has index `p` in `Hdg(X)` (the kernel of `x ↦ x·η mod p` on `Hdg(X)`), so `|disc Hdg°| = p^{E+1}`. By (1), `Hdg° = I_T·e`, and its image in `Õ_𝔅` is the ideal `I_T·A_𝔅` of `A_𝔅`, of index `|Z[G]/(I_𝔅 + I_T)| = p^E`. So `[Õ_𝔅 : M_𝔅] = p^{δ_𝔅 + E}`, and Lemma 3.3 gives `E + 1 = −κB + 2δ_𝔅 + 2E`.

(iii) The same with `T(X) = I_𝔅·e` and `|disc T(X)| = p^E`: `E = −κt + 2δ_T + 2E`. ∎

**Remark.** The equality of orders in Theorem 1 has, for prime degree, a second proof. Put `D := log_p |Z[G]/(I_𝔅 + I_T)|`. Without Theorem 1, Lemma 3.3 gives `E + 1 = −κB + 2δ_𝔅 + 2D` and `E = −κt + 2δ_T + 2D` (the second uses only `|disc T(X)| = |disc Hdg(X)|`, step (a) of the proof of Theorem 1). Adding them, with (i) and Lemma 3.2, gives `E = D`. Statement (iv) says that `E` is the intersection number at `p` of the arithmetic curve of the Hodge characters with the curve of the others, in the form «`δ` of the union minus the `δ`'s of the parts».

**The same for any set of characters.** Let `Y ⊂ 𝔄` be stable under `F_p^*`, and `Λ_Y ⊂ H` the lattice of the classes whose components lie in the eigenspaces of `Y` and of the trivial character. If `Λ_Y` contains a class of degree `1`, the proofs of Theorem 1 and of (ii) apply word for word, with `Λ_Y`, `Λ_Y ∩ H° = I_{𝔄∖Y}·e` and `Λ_Y^⊥ = I_Y·e` in the place of `Hdg(X)`, `Hdg°` and `T(X)`: `|disc Λ_Y| = |Z[G]/(I_Y + I_{𝔄∖Y})|` is a power of `p`, and

> `v_p(disc Λ_Y) = 1 + κ·|[Y]| − 2δ_Y`. (2)

---
## 4. The tangent cone of the Hodge order

It remains to compute `δ_𝔅`. Let `S := F_p[x_1, …, x_r]` be the ring of polynomial functions on the space of characters, and `x_0 := −(x_1 + … + x_r)`. For `Y` as in 3.1 let `I([Y]) ⊂ S` be the homogeneous ideal of the points `[Y]`, `S_Y := S/I([Y])`, and `h_{[Y]}` its Hilbert function; `h_{[Y]}(j) = |[Y]|` for `j` large.

> **Theorem 3.** (a) `δ_𝔅 ≤ Σ_{j ≥ 0} (B − h_{[𝔅]}(j))`. Hence
>
> `E_k(p) ≥ 1 + κ·B − 2·Σ_{j ≥ 0} (B − h_{[𝔅]}(j)) ≥ 1 + κ·B − 2·Σ_i ⌊i/(p−1)⌋·a(i)`,
>
> where `a` is the Hilbert function of the ring in (C) below.
>
> (b) Suppose that
>
> (C) `dim_{F_p} F_p[x_0, …, x_{N−1}]/(e_1, e_3, …, e_{N−1}; x_0^{p−1}, …, x_{N−1}^{p−1}) = Q_k(p)`,
>
> where `e_j` is the `j`-th elementary symmetric polynomial. Then equality holds in (a), and
>
> **`E_k(p) = 1 + (2k(p−2) − 1)·B − 2·Σ_i ⌊i/(p−1)⌋·a(i) = 1 − B + 2·Σ_{j=0}^{k(p−2)−1} h(j)`**,
>
> where `a` is the Hilbert function of the ring in (C) and `h(j) := Σ_{s ≥ 0} a(j − s(p−1))`.
>
> (c) (C) holds for every odd prime `p` and every `k` by [CL, Note, Proposition 3.1], which rests on [BRR, Proposition 2.12]. Independently of [BRR], (C) was verified by machine in the 22 cells of Table 6.

The ring in (C) is the ring of Theorem A of [CL] with the even box `p − 1`. By [CL, Note] it is, over an infinite field, the space of coinvariants of the centralizer (as an algebraic group) of a regular unipotent element of `Sp_{p−1}` in the `(2k+2)`-nd tensor power of the vector representation.

**4.1 Proof of (a).** Tensor everything with `Z_p`; from here on `Z[G]`, `I_𝔅`, `A_𝔅`, `Õ_𝔅` stand for their tensor products with `Z_p`. Filter `Õ_𝔅` by the powers of `π`: `gr Õ_𝔅 = Π_{[a]} F_p[ϖ]`, with `ϖ` the class of `π`. Give `A_𝔅 ⊂ Õ_𝔅` the induced filtration `A_𝔅 ∩ π^j Õ_𝔅`. Since `A_𝔅 ⊃ π^J Õ_𝔅` for `J` large,

> `δ_𝔅 = Σ_{j ≥ 0} (B − dim gr_j A_𝔅)`. (3)

Put `y_ν := u_ν − 1 ∈ Z[G]`. Its image in `Õ_𝔅` is `(ζ^{a_ν} − 1)_a`, and `ζ^{a_ν} − 1 ≡ a_ν·π mod π^2`. So for a homogeneous `f ∈ S` of degree `j`, the element `f(y_1, …, y_r)` (with coefficients lifted to `Z`) lies in `π^j Õ_𝔅`, and its class in `gr_j` is `(f(a)·ϖ^j)_a`. The map `f ↦ (f(a)ϖ^{deg f})_a` has kernel `I([𝔅])`. Therefore `S_𝔅 ⊂ gr A_𝔅`, `dim gr_j A_𝔅 ≥ h_{[𝔅]}(j)`, and the first inequality of (a) follows from (3) and Theorem 2(ii).

For the second inequality put `z := x_0^{p−1}`. `S_𝔅` embeds in `Π_{[a]} F_p[ϖ]`, where `z` acts as `ϖ^{p−1}`; so `S_𝔅` is a finitely generated graded torsion-free module over `F_p[z]`, hence free, on generators whose degrees are counted by the Hilbert function `a′` of `S_𝔅/zS_𝔅`. So `h_{[𝔅]}(j) = Σ_{s ≥ 0} a′(j − s(p−1))`, `Σ_{i ≡ j mod (p−1)} a′(i) = B` for every `j`, and `Σ_j (B − h_{[𝔅]}(j)) = Σ_i ⌊i/(p−1)⌋·a′(i)`. The forms `e_j(x_0, …, x_{N−1})` with `j` odd and `x_ν^{p−1} − x_0^{p−1}` vanish on `[𝔅]` (proof of Lemma 4.4), so the ring in (C) maps onto `S_𝔅/zS_𝔅`, and `a′ ≤ a` in every degree. ∎

**4.2 Three lemmas for (b).** On `Z_p[G]` let `Fil^j` be the `Z_p`-span of the elements `p^c·y^e` (`y^e` a monomial in `y_1, …, y_r`) with `c(p−1) + |e| ≥ j`. It is a decreasing filtration by ideals, `Fil^i·Fil^j ⊂ Fil^{i+j}`, and `Fil^j` maps into `π^j Õ_𝔅`. Note that `y_0 ∈ Fil^1` and `y_0 ≡ −(y_1 + … + y_r) mod Fil^2`, because `u_0 = Π_{i ≥ 1}(1 + y_i)^{−1}`. For a form `f ∈ S` of degree `d` we write `f(y)` for `f(y_1, …, y_r)` with the coefficients lifted to `Z_p`; another lift changes it by `p` times a form of degree `d`, an element of `Fil^{d+p−1}`.

**Lemma 4.3 (lifts).** Put `N_ν := 1 + u_ν + … + u_ν^{p−1}` and `τ_ν := u_ν − u_ν^{−1}`. Then:
- `N_ν ∈ I_𝔄 ⊂ I_𝔅`, and `N_ν ≡ p + y_ν^{p−1} mod Fil^p`;
- for `j` odd, `E_j := 2^{−j}·e_j(τ_0, …, τ_{N−1}) ∈ I_𝔅`, and `E_j ≡ e_j(y_0, …, y_{N−1}) mod Fil^{j+1}`.

*Proof.* `χ_a(N_ν) = 0` when `a_ν ≠ 0`, and `N_ν = ((1 + y_ν)^p − 1)/y_ν = y_ν^{p−1} + p + Σ_{i=2}^{p−1} C(p, i)·y_ν^{i−1}`, where each term of the sum has weight at least `p`. For `a ∈ 𝔅` the numbers `s_ν := ζ^{a_ν} − ζ^{−a_ν}` come in pairs `{s, −s}`, so `Π_ν (1 + s_ν X)` is even in `X` and the odd elementary symmetric functions of the `s_ν` vanish: `χ_a(E_j) = 0`. Finally `τ_ν = (1 + y_ν) − (1 + y_ν)^{−1} ≡ 2y_ν mod Fil^2`. ∎

**Lemma 4.4 (the ideal of the Hodge points).** Assume (C). Then `I([𝔅])` is generated by the forms `e_j(x_0, …, x_{N−1})`, `j` odd, `3 ≤ j ≤ N − 1`, and `x_ν^{p−1} − x_0^{p−1}`, `1 ≤ ν ≤ N − 1`. Moreover `S_𝔅` is a free module over `F_p[x_0^{p−1}]`, with a basis that lifts a homogeneous basis of the ring in (C); in particular `h_{[𝔅]}(j) = h(j)`.

*Proof.* Let `𝒮` be the quotient of `S` by those forms. They vanish on `[𝔅]`: at a point with all coordinates in `F_p^*`, `x_ν^{p−1} = x_0^{p−1}`; and on a character that can be matched in pairs the odd elementary symmetric functions vanish. So `𝒮 → S_𝔅` is surjective. Put `z := x_0^{p−1}`. `S_𝔅` embeds in `Π_{[a]} F_p[ϖ]`, where `z` acts as `ϖ^{p−1}`, so `S_𝔅` is a finitely generated graded torsion-free `F_p[z]`-module, hence free; its rank is `(p−1)·B = Q_k(p)` (the cokernel of the embedding has finite length, and `Π F_p[ϖ]` has rank `(p−1)B`). On the other hand `𝒮/z𝒮` is the ring in (C), of dimension `Q_k(p)`, so by the graded Nakayama lemma `𝒮` is generated over `F_p[z]` by `Q_k(p)` homogeneous elements. A surjection `F_p[z]^{Q} → 𝒮 → S_𝔅 ≅ F_p[z]^{Q}` is an isomorphism. ∎

**Lemma 4.5 (the induced filtration is the quotient filtration).** Assume (C). Then `A_𝔅 ∩ π^j Õ_𝔅` is the image of `Fil^j`, for every `j`.

*Proof.* Let `w ∈ Z_p[G]` have image in `π^j Õ_𝔅`, and let `d ≤ j` be maximal with `w ∈ Fil^d + I_𝔅`. Suppose `d < j`, and write `w = w_d + w′ + i` with `i ∈ I_𝔅`, `w′ ∈ Fil^{d+1}` and `w_d = Σ c_{c,e}·p^c y^e` over the pairs with `c(p−1) + |e| = d` (coefficients in `Z_p`). Since `p ≡ −π^{p−1} mod π^p` in `Z[ζ]` (Wilson), the class of the image of `w_d` in `gr_d Õ_𝔅` is that of the form `f := Σ c̄_{c,e}·(−x_0^{p−1})^c x^e ∈ S_d`; it is zero because `d < j`, so `f ∈ I([𝔅])_d` (`f` may be the zero form, when the terms of `w_d` cancel; the argument covers this case). By Lemma 4.4, `f = Σ φ_i g_i` with `g_i` among the generators listed there. By Lemma 4.3 each `g_i` has a lift `g̃_i ∈ I_𝔅` with `g̃_i ≡ g_i(y) mod Fil^{deg g_i + 1}` (namely `E_j`, and `N_ν − N_0`). So `v := Σ φ_i(y)·g̃_i ∈ I_𝔅` and `v ≡ f(y) mod Fil^{d+1}`. Also `p^c y^e − (−y_0^{p−1})^c y^e ∈ N_0·Fil^{d−(p−1)} + Fil^{d+1} ⊂ I_𝔅 + Fil^{d+1}`. Hence `w ∈ Fil^{d+1} + I_𝔅`, against the choice of `d`. ∎

**Remark (tangent cone).** In `A_𝔅` the relation `N_0 = 0` reads `p·(1 + c) = −y_0^{p−1}` with `c` in the maximal ideal `𝔪` of `A_𝔅`; so `p ∈ 𝔪^{p−1}`, and the image of `Fil^j` in `A_𝔅` is `𝔪^j`. With Lemma 4.5, the filtration induced from `Õ_𝔅` is the `𝔪`-adic one, and `gr_𝔪 A_𝔅 = S_𝔅`: the cone over `[𝔅]` is the tangent cone of `Spec A_𝔅` at its closed point, in the usual sense.

**4.6 Proof of (b).** By Lemma 4.5, `gr_j A_𝔅` is spanned by the classes of the `p^c y^e` with `c(p−1) + |e| = j`, which lie in the image of `S` (the class of `p` is that of `−x_0^{p−1}`). With 4.1, `gr A_𝔅 = S_𝔅`, and (3) gives `δ_𝔅 = Σ_j (B − h_{[𝔅]}(j))`. By Lemma 4.4, `h_{[𝔅]}(j) = Σ_{s ≥ 0} a(j − s(p−1))`, and `Σ_{i ≡ j mod (p−1)} a(i) = B` for each residue class. So `B − h(j) = Σ_{i > j, i ≡ j} a(i)` and `Σ_j (B − h(j)) = Σ_i ⌊i/(p−1)⌋·a(i)`. This is the first form.

For the second form we need `a(i) = 0` for `i > (k+1)(p−2)`. Over `Q`, multiplication by `e_1 = x_0 + … + x_{N−1}` on `Q[x]/(x_i^{p−1})` is the raising operator of an `sl_2`-module in which a monomial of degree `i` has weight `2i − N(p−2)`; it is onto the part of positive weight, so the quotient by `e_1` vanishes in degrees `> N(p−2)/2`. The Hilbert function of the ring in (C) is the same over `F_p` and over `Q`: each graded piece of the ring over `Z` has rank at most its dimension modulo `p`, and the total dimensions agree ((C), and [CL, Note, Proposition 3.1] in characteristic `0`). Hence `h(j) = B` for `j ≥ k(p−2)`, and `Σ_j (B − h(j)) = k(p−2)·B − Σ_{j < k(p−2)} h(j)`. ∎

---
## 5. One matching, cubics, surfaces

> **Theorem 4 (one matching).** Let `p` be an odd prime, `J` a matching of `{0, …, N−1}` in pairs, and `Λ_J ⊂ H` the lattice spanned by the classes of the `p^{k+1}` standard spaces of `J`. Then
> `|disc Λ_J| = p^{1 + (p−1)^k·(k(p−2) − 1)}`.

*Proof.* Let `Y = 𝔅_J` be the set of the characters with `a_i + a_j = 0` for the pairs of `J` and no zero coordinate; `|Y| = (p−1)^{k+1}`. The `p^{k+1}` spaces of `J` form one orbit of `G`, with stabilizer `{g : g_i = g_j on the pairs of J}`; so the characters that occur in `Λ_J ⊗ C` are trivial on that subgroup, that is, they have `a_i + a_j = 0` on the pairs, and those that occur in `H` are `0` and the elements of `Y`. `Λ_J` is primitive, of rank `(p−1)^{k+1} + 1` [DS, Corollary 1.6]; so all of them occur and `Λ_J` is the lattice `Λ_Y` of (2). It contains a standard space, of degree `1`. `[Y]` is the set of the `(p−1)^k` points of a projective space `P^k(F_p)` with no zero coordinate; its ideal is generated by the linear forms `x_i + x_j` and the forms `w_i^{p−1} − w_0^{p−1}` in the coordinates `w_0, …, w_k` of that space (a reduced complete intersection of the right degree). These generators lift to `I_Y` with the right leading forms: `u_iu_j − 1 ≡ y_i + y_j mod Fil^2`, and `N_ν − N_0`. So the proof of Lemma 4.5 applies without (C), `gr A_Y = S_Y`, and `δ_Y = Σ_j ((p−1)^k − h_{[Y]}(j))` with `Σ_j h_{[Y]}(j)X^j = (1 + X + … + X^{p−2})^k/(1 − X)`. The sum is the derivative at `1` of `(1 + X + … + X^{p−2})^k`, that is `δ_Y = k(p−1)^k(p−2)/2`. By (2), `|disc Λ_J|` is a power of `p` and `v_p(disc Λ_J) = 1 + (2k(p−2) − 1)(p−1)^k − k(p−1)^k(p−2)`. ∎

**Remark (a second computation of `δ_Y`, due to the cold reader).** `A_Y = Z[G]/I_Y` is the group ring of `(Z/p)^{k+1}` modulo the cyclotomic polynomials `Φ_p(t_i)`, that is, `Z[ζ]^{⊗(k+1)}`, whose trace form has discriminant `disc(Z[ζ])^{(k+1)(p−1)^k}`, against `disc(Z[ζ])^{(p−1)^k}` for `Õ_Y`. Hence `2δ_Y = k(p−2)(p−1)^k`, with no use of §4.

> **Corollary 5 (Fermat cubics).** For every `k ≥ 1`, `|disc Hdg(X^3_{2k})| = 3^{2·4^k + 1 − 3·C(2k+1, k)}`: the exponents are `0, 3, 24, 135, 663, 3045, 13464, …`.

*Proof.* For `p = 3` the ring in (C) is `F_3[x]/(e_odd; x_i^2)`, and (C) holds by [CL, Note, Proposition 3.1] (here the group is `SL_2`); for `2 ≤ k ≤ 6` it was also verified by machine. Its Hilbert function is that over `Q`. Modulo the squares, Newton's identities read `j·e_j = e_1·e_{j−1}`, so over `Q` the ring is `Q[x]/(e_1; x_i^2)`, and by the `sl_2` argument of 4.6, `a(i) = C(N, i) − C(N, i−1)` for `i ≤ k + 1` and `a(i) = 0` beyond. Hence `h(j) = C(2k+1, j)` for `j ≤ k`, `B = C(2k+1, k)`, and `E = 1 − B + 2·Σ_{j=0}^{k−1} C(2k+1, j) = 1 − C(2k+1, k) + 2·(4^k − C(2k+1, k))`. ∎

For `k = 2` this is `27`, the row `1^{19}·3·9` of [AMV, Table 1].

**Surfaces.** For `k = 1`, `[𝔅]` is the set of the `3(p−2)` points with no zero coordinate on the three lines `x_0 + x_i = 0` of `P^2(F_p)`: `p − 1` points on each line, the three vertices of the triangle counted once. A form of degree `j ≤ p − 2` that vanishes on `[𝔅]` vanishes on the three lines, so `h_{[𝔅]}(j) = 3j` for `1 ≤ j ≤ p − 2`, and `Σ_j (B − h_{[𝔅]}(j)) = (3p^2 − 9p + 4)/2`. Theorem 3(b) then gives `E_1(p) = 1 + (2p − 5)·3(p − 2) − (3p^2 − 9p + 4) = 3(p − 3)^2`: the Watermark theorem [WDL], which has an independent proof verified in Lean.

---
## 6. The numbers

**The polynomials (observed, not proved).** With `x = p − 3`:

| `k` | dimension | `E_k`, as a polynomial in `x = p − 3` |
|---|---|---|
| 1 | 2 | `3x^2` |
| 2 | 4 | `30x^3 + 30x + 3` |
| 3 | 6 | `315x^4 − 420x^3 + 1225x^2 − 504x + 24` |
| 4 | 8 | `3780x^5 − 14175x^4 + 47250x^3 − 64890x^2 + 40830x + 135` |
| 5 | 10 | `51975x^6 − 374220x^5 + 1767150x^4 − 4546080x^3 + 6464271x^2 − 3788994x + 663` |
| 6 | 12 | `810810x^7 − 9459450x^6 + 63693630x^5 − 256351095x^4 + 628533906x^3 − 855737883x^2 + 492167858x + 3045` |
| 7 | 14 | `14189175x^8 − 243243000x^7 + 2260808550x^6 − 13038905880x^5 + 48478915485x^4 − 112810998300x^3 + 148705398465x^2 − 83774680984x + 13464` |

For `k = 1` this is a theorem for every `p`. For `k ≥ 2`, each row was obtained by interpolation on `k + 2` primes and then tested on at least four primes not used in the fit; no test failed (`ajuste.log`; the primes go up to `43`). **What was interpolated.** The values used are those of the walk statistic (engine 4 of §8). That statistic is the Hilbert function of the ring in (C) — hence, by Theorem 3, gives `E_k(p)` — in the 22 cells of Table 6, where the ring itself was computed; for the even box this identification is proved nowhere in general ([CL, Note, Theorem 7.1] proves it for odd boxes). So the rows are the formula of Theorem 3 at the cells of Table 6 (`k = 2`: the ten primes `3, …, 31`; `k = 3`: `3, 5, 7, 11`; `k = 4`: `3, 5`; `k = 5, 6`: `3`), the closed form of Corollary 5 at `p = 3` for every `k`, and the walk statistic elsewhere. In every row the leading coefficient is `k·(2k+1)!!` and the constant term is `E_k(3)`. That `E_k` is a polynomial in `p` is Conjecture P of §9.

**Values.** In the following cells there was no lattice computation. By Theorem 3 (with (C) verified by machine in each of them, except the last, which is Corollary 5):

| variety | `disc Hdg(X)` | rank |
|---|---|---|
| Fermat fourfold of degree 11 | `± 11^{15603}` | 10901 |
| Fermat fourfold of degree 13 | `± 13^{30303}` | 19921 |
| Fermat sixfold of degree 5 | `± 5^{5596}` | 4901 |
| Fermat sixfold of degree 7 | `± 7^{71368}` | 44731 |
| Fermat eightfold of degree 5 | `± 5^{94395}` | 63505 |
| Fermat cubic of dimension 12 | `± 3^{3045}` | 3433 |
| Fermat cubic of dimension 14 | `± 3^{13464}` | 12871 |

Two of them, the sixfold of degree `5` and the cubic of dimension `12`, were confirmed by the direct computation of `δ_𝔅` in the group ring (Table 2), which uses Theorem 2 only.

**A law that is false.** Let `t` be the number of Galois orbits in `T`, the rank over `Z[ζ_p]` of the transcendental lattice. On every surface `E = 3(p−3)^2 = 3t`, and on the Fermat cubics `E_k(3) = 3t` as well. But at `(4, 5)`, `E = 303` and `3t = 315`; at `(4, 7)`, `E = 2043` and `3t = 2403`. By Theorem 2(iii) the correct statement is `E = κ·t − 2δ_T`.

---
## 7. What the theorems say, in one paragraph

`Spec Z[G]` is a union of arithmetic curves, one for each Galois orbit of characters, all meeting over `p`. The Hodge characters cut out one curve, the other primitive characters another. Theorem 1 says that the discriminant group of `Hdg(X)` is the ring of functions on the intersection of these two curves. Theorem 2 computes its length by the classical formula for the intersection number of two curves through their delta invariants; the form `θ = Π(1 − u_ν)` of Pham contributes the constant `κ`. Theorem 3 says that the Hodge curve is as singular as its tangent cone, the cone over the Hodge points in `P^{2k}(F_p)`; and that cone is the one object that [CL] is about, the union of the `(2k+1)!!` matching subspaces, with the box `p − 1`. For a single matching the cone is a complete intersection and everything is explicit (Theorem 4).

---
## 8. Verification

All the runs that are used stay under 1.2 GB and 10 minutes on a laptop; the runs stopped by the guard are not used, and their logs are kept and say so. Scripts and logs: `engines/` (in the repository; `corpus4/regla296_conjetura/` and `corpus4/regla297_teorema/` in the working tree).

**Seven engines.**
1. **Lattice.** The Gram matrix of all standard `k`-spaces (`P·P′ = (1 − (1−p)^c)/p`, with `c − 1` the dimension of `P ∩ P′`), then its Smith form over `Z/p^M`. It reproduces the published rows of [AMV, Table 1] with the complete lists of elementary divisors.
2. **Points.** The Hilbert functions of the point sets `[𝔄], [𝔅], [T] ⊂ P^{2k}(F_p)`, by linear algebra over `F_p`.
3. **Ring.** The Hilbert function of the ring in (C) by Macaulay2, over `F_p` (and over `Q` and `F_{32003}` in some cells).
4. **Walks.** The same Hilbert function from the fibre-rank statistic on closed walks of [CL, Note]; no Gröbner basis. It agrees with engine 3 in the 22 cells where both ran.
5. **Orders.** New in this version. The matrix of the evaluations `Z[G] → Õ_Y` for `Y = 𝔄, 𝔅, T`, and its Smith form over `Z/p^M`: this gives `δ_𝔄, δ_𝔅, δ_T` straight from the definition, with no geometry and no Hilbert function.
6. **Discriminant group.** New. The abelian group `Z[G]/(I_𝔅 + I_T)`, for any degree `m`, by two programs: exactly over `Z` (integer kernels and a Smith form; small cells), and prime by prime from the indices of Lemma 3.2 (`grupo_lector_en_frio.py`, written by the cold reader of §10 and run again here).
7. **Pham model.** New. The Gram matrices of `H° = Z[G]e`, of `Hdg° = I_T·e` and of `T(X) = I_𝔅·e`, built from the form `θ` of §1.3 and nothing else, and their Smith forms at `p`. This tests §1.3 from end to end: it has to return `|disc H°| = p` and the published rows of [AMV, Table 2].

**Table 1. The exponent `E = v_p(disc Hdg(X))`: lattice against Theorem 3.**

| `(n, p)` | elementary divisors of `Hdg(X) = L(X)` (`p`-part) | `E`, lattice | source of the lattice value | `E`, Theorem 3 |
|---|---|---|---|---|
| (2, 5) | `1^{26} · 5^{10} · 25` | 12 | [AMV, Table 1]; engine 1 | 12 |
| (2, 7) | `1^{48} · 7^{38} · 49^5` | 48 | [AMV, Table 1]; engine 1 | 48 |
| (2, 11) | `1^{96} · 11^{158} · 121^{17}` | 192 | [AMV, Table 1] | 192 |
| (2, 13) | `1^{120} · 13^{254} · 169^{23}` | 300 | [AMV, Table 1] | 300 |
| (4, 3) | `1^{19} · 3 · 9` | 3 | [AMV, Table 1]; engine 1 | 3 |
| (4, 5) | `1^{166} · 5^{174} · 25^{54} · 125^7` | 303 | [AMV, Table 1]; engine 1 | 303 |
| **(4, 7)** | `1^{443} · 7^{854} · 49^{504} · 343^{59} · 2401` | **2043** | **engine 1, new** (two runs, independent pivot orders) | 2043 |
| **(6, 3)** | `1^{56} · 3^7 · 9^7 · 27` | **24** | **engine 1, new**; [AMV, Table 2] gives `Hdg°`: `1^{54} · 3^8 · 9^7 · 27`, exponent `25 = 24 + 1` | 24 |
| (8, 3) | `Hdg°`: `1^{172} · 3^{35} · 9^{34} · 27^{11}` | 135 | [AMV, Table 2], `136 − 1` | 135 |
| (10, 3) | `Hdg°`: `1^{559} · 3^{144} · 9^{144} · 27^{76} · 81` | 663 | [AMV, Table 2], `664 − 1` | 663 |

In the last three rows we use `|disc Hdg°| = p·|disc Hdg(X)|` (proof of Theorem 2(ii)). Engine 1 computes the lattice `L(X)` of the linear spaces; `L(X) = Hdg(X)` in these cells by [Shi79] and the primitivity of `L(X)`, which [DS, §5] verified by computer at `(4, 3), (4, 5), (4, 7), (6, 3)` (and [CL] proves in general).

**Table 2. Engine 5: the delta invariants, and the four identities of Theorem 2.**

| `(n, p)` | `α` | `B` | `t` | `κ` | `δ_𝔄` | `δ_𝔅` | `δ_T` | `2δ_𝔄 − 1 − κα` | `1 + κB − 2δ_𝔅` | `κt − 2δ_T` | `δ_𝔄 − δ_𝔅 − δ_T` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| (2, 5) | 13 | 9 | 4 | 5 | 33 | 17 | 4 | 0 | 12 | 12 | 12 |
| (2, 7) | 31 | 15 | 16 | 9 | 140 | 44 | 48 | 0 | 48 | 48 | 48 |
| (2, 11) | 91 | 27 | 64 | 17 | 774 | 134 | 448 | 0 | 192 | 192 | 192 |
| (2, 13) | 133 | 33 | 100 | 21 | 1397 | 197 | 900 | 0 | 300 | 300 | 300 |
| (4, 3) | 11 | 10 | 1 | 3 | 17 | 14 | 0 | 0 | 3 | 3 | 3 |
| (4, 5) | 205 | 100 | 105 | 11 | 1128 | 399 | 426 | 0 | 303 | 303 | 303 |
| (6, 3) | 43 | 35 | 8 | 5 | 108 | 76 | 8 | 0 | 24 | 24 | 24 |
| (8, 3) | 171 | 126 | 45 | 7 | 599 | 374 | 90 | 0 | 135 | 135 | 135 |
| (10, 3) | 683 | 462 | 221 | 9 | 3074 | 1748 | 663 | 0 | 663 | 663 | 663 |
| (4, 7) | 1111 | 310 | 801 | 19 | | 1924 | | | 2043 | | |
| **(6, 5)** | 3277 | 1225 | 2052 | 17 | | 7615 | | | **5596** | | |
| **(12, 3)** | 2731 | 1716 | 1015 | 11 | | 7916 | | | **3045** | | |

In the last three rows only `δ_𝔅` was computed. For `(6, 5)` and `(12, 3)` no lattice computation exists; the values of `δ_𝔅` are those that Theorem 3 gives from the Hilbert function of the ring.

**Table 3. Theorem 4 against the lattice (engine 1 restricted to one matching).**

| `(n, p)` | rank | elementary divisors (`p`-part) | `v_p(disc)`, lattice | `1 + (p−1)^k(k(p−2) − 1)` |
|---|---|---|---|---|
| (2, 7) | 37 | `1^{12} · 7^{25}` | 25 | 25 |
| (4, 5) | 65 | `1^{11} · 5^{27} · 25^{27}` | 81 | 81 |
| (4, 7) | 217 | `1^{17} · 7^{75} · 49^{125}` | 325 | 325 |
| (4, 11) | 1001 | `1^{29} · 11^{243} · 121^{729}` | 1701 | 1701 |
| (6, 3) | 17 | `1^6 · 3^6 · 9^4 · 27` | 17 | 17 |
| (6, 5) | 257 | `1^{14} · 5^{54} · 25^{108} · 125^{81}` | 513 | 513 |

**Table 4. Theorem 1: the group `Z[G]/(I_𝔅 + I_T)` (engine 6) against the discriminant group of `Hdg(X)`.**

| `(n, m)` | `Z[G]/(I_𝔅 + I_T)` | discriminant group of `Hdg(X)` | source |
|---|---|---|---|
| (2, 4) | `(Z/8)^2` | `(Z/8)^2` | [AMV, Table 1], row `1^{18} · 8^2` |
| (2, 5) | `(Z/5)^{10} × Z/25` | `(Z/5)^{10} × Z/25` | [AMV, Table 1] |
| (4, 3) | `Z/3 × Z/9` | `Z/3 × Z/9` | [AMV, Table 1] |
| (6, 3) | `(Z/3)^7 × (Z/9)^7 × Z/27` | `(Z/3)^7 × (Z/9)^7 × Z/27` | engine 1 |
| (2, 6) | `Z/4 × (Z/12)^9 × (Z/36)^9 × Z/108`, of order `2^{40}·3^{30}` | order `2^{40}·3^{30}` | [ABB, Remark 3.5] (the discriminant of `T(X)`; the group is not given there) |

**Table 4 bis. Remark (ii) to Theorem 1 at composite degrees: the group `Z[G]/(I_𝔇 + I_{𝔄∖𝔇})` (matchable characters) against the lattice of linear cycles of [AMV, Table 1].**

| `(n, m)` | `Z[G]/(I_𝔇 + I_{𝔄∖𝔇})` | [AMV, Table 1] |
|---|---|---|
| (2, 6) | `(Z/4)^{12} × (Z/3)^{21} × (Z/9)^3 × Z/27` | `3^{13} · 12^8 · 36^3 · 108` |
| (2, 8) | `(Z/2)^{12} × (Z/8)^{48} × (Z/16)^2 × (Z/32)^8 × (Z/64)^4` | `2^{12} · 8^{48} · 16^2 · 32^8 · 64^4` |
| (2, 9) | `(Z/3)^7 × (Z/9)^{72} × (Z/27)^7 × (Z/81)^{11}` | `3^7 · 9^{72} · 27^7 · 81^{11}` |
| (2, 10) | `(Z/2)^{96} × (Z/4)^{24} × (Z/5)^{127} × (Z/25)^{10} × Z/125` | `5^{18} · 10^{96} · 20^{13} · 100^{10} · 500` |
| (4, 4) | `(Z/2)^2 × (Z/4)^4 × (Z/8)^{30} × (Z/16)^4 × (Z/32)^2` | `2^2 · 4^4 · 8^{30} · 16^4 · 32^2` |

The two columns are the same groups. At `(4, 4)` the Hodge characters and the matchable characters give the same group.

**Table 5. Engine 7: the lattices of §1.3 built from Looijenga's form (`p`-parts of the elementary divisors).**

| `(n, p)` | `H°` | `Hdg° = I_T·e` | `T(X) = I_𝔅·e` | against |
|---|---|---|---|---|
| (2, 5) | `1^{51} · 5` | `1^{24} · 5^{11} · 25` | `1^5 · 5^{10} · 25` | `T(X)`: the group of `Hdg(X)` in [AMV, Table 1] |
| (4, 3) | `1^{21} · 3` | `1^{17} · 3^2 · 9` | `3 · 9` | the same |
| (6, 3) | `1^{85} · 3` | `1^{54} · 3^8 · 9^7 · 27` | `1 · 3^7 · 9^7 · 27` | `Hdg°`: the row `(6, 3)` of [AMV, Table 2]; `T(X)`: engine 1 |
| (8, 3) | `1^{341} · 3` | `1^{172} · 3^{35} · 9^{34} · 27^{11}` | `1^{11} · 3^{34} · 9^{34} · 27^{11}` | `Hdg°`: the row `(8, 3)` of [AMV, Table 2] |

So the discriminant group of `Hdg(X)` for the Fermat cubic eightfold is `(Z/3)^{34} × (Z/9)^{34} × (Z/27)^{11}`, of order `3^{135}`; [AMV] give the primitive lattice only.

**Table 6. Condition (C), by machine (engine 3, in characteristic `p`).** `dim = Q_k(p)` and top degree `(k+1)(p−2)` in the cells `(n, p)`: `(2, 5), (2, 7), (2, 11), (2, 13)`; `(4, 3), (4, 5), (4, 7), (4, 11), (4, 13), (4, 17), (4, 19), (4, 23), (4, 29), (4, 31)`; `(6, 3), (6, 5), (6, 7), (6, 11)`; `(8, 3), (8, 5)`; `(10, 3)`; `(12, 3)`.

---
## 9. Two conjectures and three problems

> **Conjecture P (the Watermark polynomials).** For every `k ≥ 1` there is a polynomial `W_k ∈ Z[x]` of degree `k + 1`, with leading coefficient `k·(2k+1)!!` and constant term `2·4^k + 1 − 3·C(2k+1, k)`, such that `E_k(p) = W_k(p − 3)` for every odd prime `p`. For `k ≤ 7`, `W_k` is the polynomial in the table of §6.

For `k = 1` this is the Watermark theorem. For `2 ≤ k ≤ 7` the evidence is the table of §6: `W_k` was fitted on `k + 2` primes and agrees with the values at the other primes computed (`k = 2`: fitted on `29, 31, 37, 41`, tested on `3, 5, 7, 11, 13, 17, 19, 23`; `k = 3`: tested on `3, …, 19`; `k = 4`: on `3, …, 17`; `k = 5, 6, 7`: on `3, 5, 7, 11`). As explained in §6, outside the cells of Table 6 these values are those of the walk statistic; that the statistic computes the Hilbert function of the ring with an even box is part of the conjecture. By Theorem 3 the conjecture is a statement about the Hilbert functions of the rings in (C), that is, about the generalized exponents of the representations of `sp_{p−1}` that occur in the `(2k+2)`-nd tensor power of the vector representation ([CL, Note]; [Lus]).

> **Conjecture S (the two curves meet as their tangent cones do).** For `Y = T` and for `Y = 𝔄`, the delta invariant of the order `A_Y` is that of its tangent cone: `δ_Y = Σ_{j ≥ 0} (|[Y]| − h_{[Y]}(j))`.

For `Y = 𝔅` this is Theorem 3(b). By Theorem 2 the left-hand sides are known: `δ_T = (κt − E)/2` and `δ_𝔄 = (1 + κα)/2`; so Conjecture S is a statement about the Hilbert functions of two explicit sets of points of `P^{2k}(F_p)`. It holds in the thirteen cells where those Hilbert functions were computed: `(2, 5), (2, 7), (2, 11), (2, 13), (4, 3), (4, 5), (4, 7), (4, 11), (6, 3), (6, 5), (8, 3), (10, 3), (12, 3)` (`conos_tangentes_A_T.log`). With Theorem 2(iv) and Theorem 3 it is equivalent to the pair of statements `Σ_j (α − h_{[𝔄]}(j)) = (1 + κα)/2` and

> `E_k(p) = dim_{F_p} S/(I([𝔅]) + I([T])) = Σ_j [h_{[𝔅]}(j) + h_{[T]}(j) − h_{[𝔄]}(j)]`:

the exponent of the discriminant is the length of the intersection of the cone over the Hodge points with the cone over the others. In those cells the algebra `S/(I([𝔅]) + I([T]))` has a symmetric Hilbert function, with last non-zero degree `2k(p−2) − 2`; for surfaces it has the Hilbert function of a complete intersection of type `(3, p−3, p−3)`, whose Bézout number is `3(p−3)^2`.

**Problem 1 (the discriminant group).** Theorem 1 gives the discriminant group as a ring, not its elementary divisors. For surfaces they are given by the *Double Ladder* theorem [WDL]. The tables show the first rows in higher dimension; for instance the exponent of the group (the characteristic of the ring `𝒟`) is `p^2` for surfaces, `p^3` at `(4, 5)` and `p^4` at `(4, 7)`. In Table 3 the groups follow a visible pattern in `u = p − 2` (in dimension 4: `(Z/p)^{3u^2} × (Z/p^2)^{u^3}`), recorded here and not claimed.

**Problem 2 (other degrees).** Theorem 1 holds for every `m`. For `m` a prime power the ring `Z_p[G]` is still local and the method of §3–§4 should apply, with the constant `κ` replaced by a sum over the orbits; for general composite `m` several primes interact. For composite `m` the lattice `Hdg(X)` can be larger than the saturation of `L(X)`: at `(2, 6)` the ranks are `86` and `62` ([ABB]; [AMV, Table 1]). None of this is done here.

**Problem 3.** A proof of (C) that does not use [BRR] ([CL, v10, Problem 7] is its odd-box companion).

---
## 10. Status, and what is not claimed

- **Proved, modulo [Ph]/[Loo, Corollary 2.2] and the classical facts on Fermat varieties quoted in §1** ([SK] for the Hodge type of the eigenlines; [Shi79], [Ran] for the Hodge characters of prime degree; [DS, Corollary 1.6] for Theorem 4): Theorem 1 (every `m ≥ 3`), Theorem 2, Theorem 3(a), Theorem 4.
- **Proved, modulo [Ph]/[Loo] and [BRR, Proposition 2.12]:** Theorem 3(b) for every `k` and every odd prime `p`; Corollary 5.
- **Proved, modulo [Ph]/[Loo] and a machine computation of one dimension:** Theorem 3(b) in the 22 cells of Table 6; in particular the values of §6.
- **Not proved:** the polynomials of §6 for `k ≥ 2` (they interpolate the walk statistic at primes up to `43`, which is the formula of Theorem 3 in the cells of Table 6: Conjecture P); Conjecture S; the problems of §9.
- **The sign** of the discriminant is not addressed.
- **Read in the original (arXiv versions):** [Loo], Proposition 2.1 and Corollary 2.2; [ABB], Proposition 2.10 and Remark 3.5; [AMV], Tables 1 and 2; [DS]; [BRR], §2 (for [CL, Note]). **Not read in the original:** [Ph] (quoted through [Loo]); [SK], [Shi79], [Ran], [Lus], [Kos] (quoted as in [CL] and [DS]); [Deg] (quoted as in [WDL]).
- **Unrefereed inputs:** [BRR] is an arXiv preprint; [CL], [CL, Note] and [WDL] are the author's and are not refereed.
- **Cold reading.** A first complete draft of this version was read cold by an independent reader (a separate AI session, without access to the working files, with the mandate to break it and to write its own code). Its verdict: *holds with corrections*; no fatal error. It re-derived Theorems 1–4, Lemmas 3.2–4.5, §4.6 and Corollary 5 line by line; read [Loo] and [BRR, Proposition 2.12] (statement, hypotheses and proof, not its inputs) and checked that the hypotheses hold for `Sp_{p−1}` in characteristic `p`; recomputed with its own engines Tables 1–4, except `δ_𝔅` at `(6, 5)`, and condition (C) in sixteen cells; and tested Theorem 1 at composite degrees (Table 4 bis is its addition). It found four errors of statement (the sentence on Hodge types in §1.3, with the second half of (1) not argued; a false sentence on `Hdg(X) ≠ L(X)`; «Theorem 1 is proved twice»; the description of what the polynomials interpolate), three small gaps (Theorem 4, Remark (ii), the lower bound in terms of `a`) and thirteen points of presentation. All of them are corrected in this text. Added after the reading, and so not read cold: engine 7 and Table 5; the rewriting of the open problems as Conjectures P and S, with the separate check of the two tangent cones. The reader could not verify: the inputs of [BRR]; (C) outside the cells computed; the polynomials for `k = 6, 7`; the originals of [SK], [Shi79], [Ran]. Its report, scripts and logs are in the repository.

---
## 11. Reproducibility

- `gram_smith.py n p [M]` — engine 1 (`SUBJ=0` for one matching, `PERM=seed` for a second pivot order).
- `hilbert2.py n p full|short` — engine 2.
- `ta_even.py k p [char]` — engine 3 (needs Macaulay2).
- `E_estadistica2.py k,p …` — engine 4; `ajuste.py` — the interpolation and its tests.
- `delta_ordenes.py n p [M]` — engine 5 (`RED=1` uses only the group elements with coordinates in `0..p−2`, which span each order over `Z_p`; `SETS=B` computes `δ_𝔅` only).
- `grupo_discriminante.py n p`, `grupo_general.py n m`, `grupo_lector_en_frio.py n m H|D` — engine 6.
- `pham_gram.py n p` — engine 7.

Longest runs: `(6, 5)`, `δ_𝔅`, 388 s and 1.0 GB; `(4, 7)` lattice, 105 s and 0.5 GB. Runs stopped by the guard are not used; their logs end with the line of the guard that says so.

---
## Acknowledgements and use of AI

The mathematics, the computations and the text of this note were produced with Claude, an AI system made by Anthropic, working under the author's direction. The author takes responsibility for the content.

## References

- **[ABB]** A. Auel, C. Böhning, H.-C. Graf von Bothmer, *The transcendental lattice of the sextic Fermat surface*, Math. Res. Lett. **20** (2013), no. 6, 1017–1031. arXiv:1306.6798. (Proposition 2.10 and Remark 3.5, read in the arXiv version.)
- **[AMV]** E. Aljovin, H. Movasati, R. Villaflor Loyola, *Integral Hodge conjecture for Fermat varieties*, J. Symbolic Comput. **95** (2019), 177–184. doi:10.1016/j.jsc.2019.02.006; arXiv:1711.02628. (Tables 1 and 2 were read in the original.)
- **[BRR]** R. Bezrukavnikov, S. Riche, L. Rider, *Modular affine Hecke category and regular unipotent centralizer*, arXiv:2005.05583 (v2, 4 July 2024). (Proposition 2.12.)
- **[CL]** R. Amichis Luengo, *The Chaise Longue Theorem*, version 10, Zenodo (2026). doi:10.5281/zenodo.22961150. With its supplementary note *The Chaise Longue Theorem and the centralizer of a regular unipotent element*, cited as [CL, Note].
- **[Deg]** A. Degtyarev, *Lines generate the Picard groups of certain Fermat surfaces*, J. Number Theory **147** (2015), 454–477. doi:10.1016/j.jnt.2014.07.020; arXiv:1305.3073. (Quoted as in [WDL].)
- **[DS]** A. Degtyarev, I. Shimada, *On the topology of projective subspaces in complex Fermat varieties*, J. Math. Soc. Japan **68** (2016), no. 3, 975–996. doi:10.2969/jmsj/06830975; arXiv:1405.4683.
- **[Kos]** B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. **85** (1963), 327–404.
- **[Loo]** E. Looijenga, *Fermat varieties and the periods of some hypersurfaces*, in: Algebraic and Arithmetic Structures of Moduli Spaces (Sapporo 2007), Adv. Stud. Pure Math. **58** (2010), 47 ff. doi:10.2969/aspm/05810047; arXiv:1005.1733. (Proposition 2.1 and Corollary 2.2.)
- **[Lus]** G. Lusztig, *Singularities, character formulas, and a `q`-analog of weight multiplicities*, Astérisque **101–102** (1983), 208–229.
- **[Ph]** F. Pham, *Formules de Picard–Lefschetz généralisées et ramification des intégrales*, Bull. Soc. Math. France **93** (1965), 333–367.
- **[Ran]** Z. Ran, *Cycles on Fermat hypersurfaces*, Compositio Math. **42** (1980/81), no. 1, 121–142.
- **[Shi79]** T. Shioda, *The Hodge conjecture for Fermat varieties*, Math. Ann. **245** (1979), no. 2, 175–184.
- **[Shi87]** T. Shioda, *Some observations on Jacobi sums*, in: Galois Representations and Arithmetic Algebraic Geometry, Adv. Stud. Pure Math. **12** (1987), 119–135. (Questions 7.2 and 7.4, p. 133, quoted as in [WDL].)
- **[SSvL]** M. Schütt, T. Shioda, R. van Luijk, *Lines on Fermat surfaces*, J. Number Theory **130** (2010), no. 9, 1939–1963. doi:10.1016/j.jnt.2010.01.008; arXiv:0812.2377. (Quoted as in [WDL].)
- **[SK]** T. Shioda, T. Katsura, *On Fermat varieties*, Tôhoku Math. J. (2) **31** (1979), no. 1, 97–115.
- **[WDL]** R. Amichis Luengo, *The Watermark and Double Ladder Theorems (Verified in Lean)*, Zenodo (2026). doi:10.5281/zenodo.23062529.

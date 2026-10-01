
## 3. What I verified, and how

### 3.1 Sources (attack 1)
- **[Loo, Proposition 2.1, Corollary 2.2]** read in `sources/Looijenga_texto.txt` (pages 4–5). The quotation in §1.3 is exact: `H°_n` is generated over `Z[μ_d^{n+2}/μ_d]` by `e′_n`, is isomorphic to `R′_{n+1} = Z[G]/(Σ_k u_ν^k, ν = 0..n+1)`, the form is `(−1)^{n(n+1)/2}⋆` and `e′⋆e′ = Π_{ν=0}^{n+1}(1 − u_ν)`. Looijenga's statement is for every degree `d`. The note replaces `(N_0, …, N_{N−1})` by `I_𝔄`; this is correct: `xe = 0` iff `xθ = 0` (non-degeneracy) iff `χ_a(x)χ_a(θ) = 0` for all `a`, and `χ_a(θ) ≠ 0` iff `a ∈ 𝔄`. Valid for composite `m`.
- **[DS, Corollary 1.6]** read in the text: rank `(m−1)^{d+1} + 1` and primitive, for every `m`; the Fermat case is [DS, Theorem 1.1(d)] with one matching. **[DS, §5]**: primitivity of `L(X)` verified by them at `(4, m)`, `3 ≤ m ≤ 12`, `(6,3), (6,4), (6,5), (8,3)`.
- **[BRR]** fetched (arXiv:2005.05583v2; `cold/BRR_2005.05583v2.pdf`, text in `cold/BRR_text.txt`). §2.4 standing assumptions: (1) derived subgroup simply connected, (2) `ℓ` good, (3) `X^*(T)/ZR` without `ℓ`-torsion; `K` algebraically closed. Proposition 2.12: for a finite-dimensional `G`-module `V` with a good filtration and `u` regular unipotent, `dim V^{Z_G(u)} = dim V^T`. For `G = Sp_{p−1}`, `ℓ = p` odd: simply connected, 2 is the only bad prime of type `C` (type `A_1` for `p = 3` has none), `X^*(T)/ZR = Z/2`. The natural module is a simple Weyl module (minuscule weight), tensor powers have good filtrations. The hypotheses hold.
- **[CL, Note]** read whole. Lemma 1.1 and Proposition 1.2 re-derived (the centralizer of the Cayley transform `g_t` is `{±1} × 𝒵`; `g_t` acts as `E(t)/E(−t)` and the span of the `(g − 1)v` is the ideal `(e_j : j odd)`; coinvariants are dual to invariants through the form). Proposition 3.1 with `q = p − 1`, `n = N` is exactly condition (C): the ring is the same and the count `N!·[y^N] I_0(2y)^{(p−1)/2}` is the number of matchable `a ∈ (F_p^*)^N`, i.e. `Q_k(p)`. I recomputed `Q_k(p)` from that series for ten cells (36, 400, 1860, 4900, 63504, 44730, 10900, …).
- **[AMV]** Tables 1 and 2 read in the rendered pdf (`cold/AMV_p2.png`, `cold/AMV_p7.png`); all rows quoted by the note are quoted correctly. Journal reference checked on arXiv (J. Symbolic Comput. 2019, doi 10.1016/j.jsc.2019.02.006).

### 3.2 Proofs, by pencil (attacks 1–5)
- **(1)** correct for every `m` (with the rewording of F1).
- **Theorem 1.** (a) `H → Hdg^∨` is onto with kernel `T` (unimodular, primitive); the form is non-degenerate on `Hdg` (`Hdg_Q = Qη ⊕ Hdg°_Q`, definite on the second summand by Hodge–Riemann). (b) injectivity: `H° ∩ (Hdg ⊕ T) = Hdg° ⊕ T` because `T ⊂ H°`; surjectivity: `H = ZP + H°`, `P·η = 1`, `P ∈ Hdg`. (c) `Z[G]e/(I_Te + I_𝔅e) = Z[G]/(I_T + I_𝔅 + I_𝔄)` and `I_𝔄 ⊂ I_T ∩ I_𝔅`. Equivariance: the maps are the inclusion and the restriction of the form. Nothing uses that `m` is odd or prime. **Correct for every `m ≥ 3`.**
- **Lemma 3.2.** `(x, y) ↦ x − y` on `A_{Y_1} × A_{Y_2}` is onto `Z[G]/(I_{Y_1}+I_{Y_2})` with kernel the diagonal image `A_Y`. Correct. «Index a power of `p`»: correct (`Z[1/p][G]` is a product of the rings `Z[1/p][ζ]`, `Z[1/p]`).
- **Lemma 3.3.** `ε(z) = p^{−r}Σ_a χ_a(z)`; only `a ∈ Y` contribute; the sum over an `F_p^*`-orbit is the trace of `Q(ζ)`; `det[Tr(x_i·c(x_j)·θ)] = ± N(θ)·disc_Tr(M_Y)`; `disc Z[ζ] = ±p^{p−2}`; `N(1−ζ^j) = p`, so `N_{K_Y/Q}(θ) = p^{N|[Y]|}`. Exponent `[−r(p−1) + (p−2) + N]·|[Y]| = −(2k(p−2) − 1)|[Y]|`. **`κ = 2k(p−2) − 1` recomputed: correct.** `θ̄ = θ` (so the form is symmetric) because `N` is even and `Πu_ν = 1`.
- **Theorem 2.** `|disc H°| = p` and `|disc Hdg°| = p^{E+1}` (index `p` of `Zη ⊕ (·)°`, because a class of degree 1 exists); (i)–(iv) follow as written. Consistency: `α` is odd, so `1 + κα` is even. Formula (2) for a general `Y`: correct (needs `Y = −Y`, true for `F_p^*`-stable `Y`).
- **Theorem 3(a).** (3) is the standard length count; `ζ^{a} − 1 ≡ aπ mod π^2`; the kernel of `f ↦ (f(a)ϖ^{deg f})` is `I([𝔅])`; direction of the inequality correct.
- **Lemma 4.3.** `N_ν = p + y^{p−1} + Σ_{i=2}^{p−1}C(p,i)y^{i−1}`, the middle terms in `Fil^p`; `(1+y)^{−1} = (1+y)^{p−1} ≡ 1 − y mod Fil^2`; `τ_ν ≡ 2y_ν`; odd `e_j` vanish on matched characters. Correct.
- **Lemma 4.4.** Torsion-free graded f.g. over `F_p[z]` ⇒ free; rank `(p−1)B`; `𝒮/z𝒮` is the ring in (C); Nakayama; a surjection between free modules of the same rank. Correct. Checked by machine in five cells (`cold/cold_lemma44.m2`): the Hilbert function of `S/(e_odd, x_ν^{p−1} − x_0^{p−1})` equals that of the points `[𝔅]` computed independently.
- **Lemma 4.5.** Wilson: `p = Π(1 − ζ^i) ≡ (p−1)!·π^{p−1} ≡ −π^{p−1} mod π^p`. Class of `p^c y^e` in `gr_d`: `((−1)^c a^e ϖ^d)`, equal to the value of `(−x_0^{p−1})^c x^e` because `a_0^{p−1} = 1`. Lifts `E_j`, `N_ν − N_0`. `p^c − (−y_0^{p−1})^c = (p + y_0^{p−1})·(element of Fil^{(c−1)(p−1)})` and `p + y_0^{p−1} ∈ N_0 + Fil^p`. The induction on `d` is sound, including the case where the leading terms cancel (`f = 0`). **Correct.** `N_0` is used exactly once, to trade `p` for `−y_0^{p−1}`; it lies in `I_𝔄`, so the same step works for any `Y ⊂ 𝔄`.
- **§4.6.** `Σ_j (B − h(j)) = Σ_i ⌊i/(p−1)⌋a(i)`: correct. Top degree: `e_1` is the raising operator on `(V_{p−2})^{⊗N}` over `Q`, onto the positive weights, so `a(i) = 0` for `i > (k+1)(p−2)`; Hilbert functions over `Q` and `F_p` agree by semicontinuity plus equality of totals; then `h(j) = B` for `j ≥ k(p−2)` and the second form follows. Correct.
- **Theorem 4.** Correct with the sentence of F5. `δ_Y = F′(1)` for `F = (1 + … + X^{p−2})^k`, i.e. `k(p−1)^k(p−2)/2`; confirmed by the independent argument of F18 and, for `k = 1`, by a hand computation on the Gram matrix.
- **Corollary 5.** Newton modulo squares: `j e_j = e_1 e_{j−1}` (over `Z`); `a(i) = C(N,i) − C(N,i−1)`; `h(j) = C(2k+1, j)` (alternating partial sums); `E = 2·4^k + 1 − 3C(2k+1,k)`: `0, 3, 24, 135, 663, 3045, 13464`. Correct, modulo (C) at `p = 3` (in characteristic 3 the identity `3e_3 = e_1e_2` is empty, so (C) is really needed).
- **Surfaces.** `3(p−2)` points, `h(j) = 3j` for `1 ≤ j ≤ p−2`, sum `(3p^2 − 9p + 4)/2`, `E = 3(p−3)^2`. Correct.
- **§6 «a law that is false»**, **Problem 3** (the identity `E = dim S/(I([𝔅]) + I([T]))` given the two tangent-cone statements; symmetric Hilbert function `1,3,4,3,1` at `(2,5)` and `1,3,6,9,10,9,6,3,1` at `(2,7)`, complete intersections `(3,2,2)` and `(3,4,4)`): checked.

### 3.3 Numbers, with my own code (attack 6)
All runs inside `engines/vigia.sh`; scripts and logs in `cold/`. Four independent routes: (L) lattice of linear spaces; (D) delta invariants from the definition; (P) Hilbert functions of the point sets; (R) the ring in (C) with Macaulay2.

| cell `(n,p)` | (L) elementary divisors of `L(X)`, `E` | (D) `δ_𝔄, δ_𝔅, δ_T` → `E` | (P) `Σ_j(B − h_{[𝔅]}(j))` | (R) dim, `E` |
|---|---|---|---|---|
| (2,3) | unimodular, rank 7 | 2, 2, 0 → 0 | 2 | 6, 0 |
| (2,5) | `1^26·5^10·25`, 12 | 33, 17, 4 → 12 | 17 | 36, 12 |
| (2,7) | `1^48·7^38·49^5`, 48 | 140, 44, 48 → 48 | 44 | 90, 48 |
| (2,11) | — | 774, 134, 448 → 192 | 134 | 270, 192 |
| (2,13) | — | 1397, 197, 900 → 300 | 197 | — |
| (4,3) | `1^19·3·9`, 3 | 17, 14, 0 → 3 | 14 | 20, 3 |
| (4,5) | `1^166·5^174·25^54·125^7`, 303 | 1128, 399, 426 → 303 | 399 | 400, 303 |
| (4,7) | `1^443·7^854·49^504·343^59·2401`, 2043 | —, 1924, — → 2043 | 1924 | 1860, 2043 |
| (6,3) | `1^56·3^7·9^7·27`, 24 | 108, 76, 8 → 24 | 76 | 70, 24 |
| (8,3) | — | 599, 374, 90 → 135 | 374 | 252, 135 |
| (10,3) | — | 3074, 1748, 663 → 663 | 1748 | 924, 663 |
| (12,3) | — | —, 7916, — → 3045 | (partial: `C(13,j)`, `j ≤ 5`) | — |
| (4,11), (4,13), (4,17), (6,5), (6,7), (8,5) | — | — | — | 10900/15603, 19920/30303, 50560/82743, 4900/5596, 44730/71368, 63504/94395 |

- In every cell where three sets were computed, the four identities of Theorem 2 hold ((i) `= 0`; (ii) = (iii) = (iv)).
- In every cell `δ_Y = Σ_j(|[Y]| − h_{[Y]}(j))` for `Y = 𝔅` (Theorem 3(b)) and also for `Y = 𝔄, T` wherever I had the full Hilbert function (nine cells; Problem 3).
- (R): dim `= Q_k(p)`, top degree `(k+1)(p−2)`, the two forms of the formula agree, in sixteen cells in characteristic `p` (fifteen of them in Table 5), and the same Hilbert function in characteristic 0 at `(4,5)` and `(6,3)`.
- Theorem 4 (route L restricted to one matching): `(2,3), (2,5), (2,7), (4,3), (4,5), (4,7), (4,11), (6,3), (6,5)`: rank and exponent as in the theorem; the six rows of Table 3 with their elementary divisors.
- Table 1 against [AMV] in the pdf: all rows agree. `(8,3)`: `35 + 68 + 33 = 136`; `(10,3)`: `144 + 288 + 228 + 4 = 664`; `(6,3)`: `8 + 14 + 3 = 25`.
- The polynomials of §6 for `k = 2, 3, 4, 5` evaluated at the cells of route (R): all equal.
- By hand: `p = 3`, `k = 1` (`E = 0`, cubic surface unimodular; `α = B = 3`, `δ = 2`); `p = 3`, `k = 2` (`E = 1 − 10 + 2(1+5) = 3`; `T(X) ≅ π^3Z[ω]`, i.e. `A_2(3)`, the known transcendental lattice of the Fermat cubic fourfold, discriminant 27, group `Z/3 × Z/9`); `p = 5`, `k = 1` (`a = 1,3,6,9,8,6,3`, `Σ⌊i/4⌋a(i) = 17`, `E = 12`).
- **I found no cell where anything fails.**

### 3.4 Theorem 1 at composite and even degrees (beyond the note)
`cold/cold_group.py` computes `Z[G]/(I_{Y_1} + I_{Y_2})` for any `m` from the indices `[Õ : A_Y + ℓ^j(A_{Y_1} × A_{Y_2})]`.

| `(n,m)`, `Y_1` | my group | published | 
|---|---|---|
| (2,4), Hodge = matchable | `(Z/8)^2` | [AMV] `1^18·8^2` ✓ |
| (4,4), Hodge = matchable | `(Z/2)^2×(Z/4)^4×(Z/8)^30×(Z/16)^4×(Z/32)^2` | [AMV] `2^2·4^4·8^30·16^4·32^2` ✓ |
| (2,6), matchable | `(Z/4)^12 × (Z/3)^21×(Z/9)^3×Z/27` | [AMV] `3^13·12^8·36^3·108` ✓ |
| (2,6), Hodge | `(Z/4)^20 × (Z/3)^9×(Z/9)^9×Z/27` | order `2^40·3^30` = `disc T_X` of Auel–Böhning–Bothmer ✓ |
| (2,8), matchable | `(Z/2)^12×(Z/8)^48×(Z/16)^2×(Z/32)^8×(Z/64)^4` | [AMV] ✓ |
| (2,9), matchable | `(Z/3)^7×(Z/9)^72×(Z/27)^7×(Z/81)^11` | [AMV] ✓ |
| (2,10), matchable | `(Z/2)^96×(Z/4)^24 × (Z/5)^127×(Z/25)^10×Z/125` | [AMV] `5^18·10^96·20^13·100^10·500` ✓ |
| (2,5), (2,7), (4,3), (6,3), Hodge | as in Table 4 / Table 1 | ✓ |

### 3.5 Claims of novelty and attributions (attack 7)
See F4, F9, F10, F17. Web searches run: discriminant of the Néron–Severi lattice of Fermat surfaces; discriminant group / transcendental lattice of Fermat varieties, group ring, Pham; Fermat cubic fourfold. Found: Schütt–Shioda–van Luijk (determinant verified for `m ≤ 81`); Auel–Böhning–Bothmer (equation (1) for surfaces; `2^40·3^30`); Laza–Zheng (`T` of the Fermat cubic fourfold, discriminant 27); Degtyarev's survey (torsion as an `Ext` of `Z[G]`-modules; no discriminant formula). I did not find Theorems 1–4 or Corollary 5. The status section (§10) is accurate except for F4, F8 and F17.

## 4. What I could not verify
- **[BRR, Proposition 2.12] itself**: I read its statement, its standing assumptions and its proof (one page, resting on [KLT], Jantzen, [Co], [BMR]); I did not check those inputs. It is an arXiv preprint.
- **(C) outside the cells computed.** I tried three cells that are not in Table 5, to look for a failure: `(k,p) = (4,7)` (killed by the guard: time, 601 s), `(5,5)` (killed: memory), `(3,13)` (RESULT_3_13). So I have no information there. Of the 22 cells of Table 5 I ran 15; not run by the ring: `(n,p) = (2,13), (4,19), (4,23), (4,29), (4,31), (6,11), (12,3)`.
- **`δ_𝔅 = 7615` at `(6,5)`** (matrix `16384 × 4900`, beyond the guard with my engine). `E(6,5) = 5596` confirmed by route (R) only.
- **`δ_𝔄` and `δ_T` at `(4,7)`, `(12,3)`** (the note does not give them either).
- **The polynomial table of §6 for `k = 6, 7`** and for every prime outside route (R); they rest on the walk statistic (F4).
- **[WDL] and its Lean verification, [CL, Main Theorem], [CL, Corollary H]**: not in my material except as claims; the note uses them only in remarks (and see F20(b)).
- **Version 1 of the note** and its predictions (F19).
- **[Shi79], [Ran], [SK], [Shi87], [Ph], [Lus], [Kos]** were not read; I used the statements as quoted. Auel–Böhning–Bothmer, Schütt–Shioda–van Luijk and Degtyarev's survey were read through an automatic summary of the arXiv text, not line by line; the quotations in F9 and F10 should be checked against the papers before they are cited.
- **The sign** of the discriminants (not claimed by the note).
- Runs of mine killed by the guard (not used): `log_delta_4_7_B.log`, `log_delta_4_7_B_run2.log`, `log_delta_10_3.log` (memory; my engine, then repaired), `log_ringC_4_7_7.log` (time), `log_ringC_5_5_5.log` (memory).

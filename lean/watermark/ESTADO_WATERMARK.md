# Watermark Theorem in Lean 4 — state (Grepy el Auditor)

Source (highest version, checked on the whole Mac): `REPO CHAISE LONGUE/hodge-fermat-campaign/THE_WATERMARK_THEOREM.md`, md5 `7efa0f0529c1be4ca00facc7f34c2cf8` (= `~/Downloads/THE_WATERMARK_THEOREM.md`, 5 Jun 2026). The `_v6` in Downloads is one sentence older (§1 on AMV). The July «WATERMARK» files (Blas, descent) are another object.

Target: for prime m ≥ 5, V := A/ker G (G the 3m²×3m² line Gram of §2) has |disc V| = m^{3(m−3)^2}.
Sanity (Macaulay2, `checks/w1_r2_*.log`): product of nonzero elementary divisors of G = 5^12, 7^48; rank V = 37, 91; rank K = 38, 56.

Aristotle project: https://aristotle.harmonic.fun/projects/884019b5-ec06-4ff7-8a7b-8d8a1f18d0a1 (created 29 Sep 2026, Chrome tab 585561209). Same cycle and stop conditions as the Chaise (`../ESTADO_ARISTOTLE.md`).

## Plan of pieces (tentative; each checked by brute force before sending)
| # | Content (paper §) | State |
|---|---|---|
| W1 | definitions (lines, G, A, K, V, form, N_j, pencils); symmetry; G·N_j = m·1; R.1; R.2 | SENT 29 Sep, checks `checks/w1_gram.log`, `w1_r2_{5,7}.log`, `w1_Gy.log` |
| W2 | Lemma C (§9): rank over F_m of SAT mod m = 9m−19 (polynomial relation count) | to write |
| W3 | Lemma P / kernel census (§3): characters, rank K = 9m−7, rank V = 3(m−1)(m−2)+1 | to write |
| W4 | Lemma T (§4) and the big determinant (§6): circulants det(mI−J) = m^{m−2}, block diagonal | to write |
| W5 | SAT ⊂ K, [SAT : K₀] = m^{9(m−2)} (§7), R.3–R.4 mK ⊆ SAT (§8) — note: SAT ⊂ K is «file-verified» in the text, not proved: Lean must prove it | to write |
| W6 | transport identity (§5) and assembly (§10): |disc V| = m^{3(m−3)^2} | to write |

## STATE AT 29 Sep ~23:00 (saved before compacting) — RAFA: «no paramos hasta que Watermark esté certificado por Lean»
- **Running:** W1 in Aristotle project 884019b5-ec06-4ff7-8a7b-8d8a1f18d0a1 (instruction ends «No sorry, no new axioms.»). Chrome tab 585561209 is on that project page.
- **When Rafa says it finished — certification cycle (same as the Chaise):**
  1. JS click `button[aria-label="Download project"]` on the project page; the tarball lands in `~/Downloads/884019b5-…-aristotle*.tar.gz` (check the exact name with `ls -t ~/Downloads | head`).
  2. Extract to `ARISTOTLE_LEAN/WATERMARK/run1/`; read ARISTOTLE_SUMMARY.md; grep for `sorry|admit|axiom|native_decide|implemented_by|unsafe|opaque`.
  3. Build locally: make `ARISTOTLE_LEAN/WATERMARK/proyecto/` from the tarball (same toolchain v4.28.0, Mathlib v4.28.0 → reuse the Mathlib cache: `lake exe cache get`, or symlink `.lake/packages` from `../proyecto_lean/output-final_aristotle/.lake/packages` if the manifest rev matches `8f9d9cff…`). Run inside `corpus4/herramientas_grepy/vigia.sh` (the Chaise builds peaked ~2.5 GB: Rafa allowed ~3 GB for Lean builds).
  4. `#check` the four statements and `#print axioms`; audit faithfulness against `pieces/w1_gram_basics.md` (G entries case by case, V = A/K, the induced form, (W1.a)–(W1.d) with their hypotheses: m ≥ 5, m prime where stated).
  5. Record: this file, `../INFORME_ARISTOTLE_v1.md` (new section «Watermark»), CLAUDE.md, memory.
  6. Write and brute-force-check W2, send it to the SAME project (upload + native textarea setter + Solve; see `../ESTADO_ARISTOTLE.md` «Sending method»).
- **Order of the next pieces:** W2 Lemma C (pure polynomial count over F_m; independent) → W3 census/Lemma P → W4 circulants + big determinant → W5 SAT ⊂ K (the step the paper only «file-verifies») + [SAT:K₀] + mK ⊆ SAT → W6 transport + assembly. Brute-force engines in `checks/` (Python + M2 G5.m2/G7.m2 already exported).
- **Also pending from Block 1:** (a) check the root README Rafa pastes on GitHub (local md5 `77b5d9021847947a5ed29a6b17c3ae72`; verify the whole repo by git hash, only `.gitkeep` may be missing); (b) check DataCite resolves 10.5281/zenodo.23045370 and 10.5281/zenodo.23045409 (`curl -s -o /dev/null -w '%{http_code}' https://api.datacite.org/dois/<doi>`).

## W1 CERTIFIED — 29 Sep ~22:00 (run 1, Aristotle run bfec8091, tarball md5 fe4ea007a2500c9aa9378553dad29dbb)
- Extracted to `run1/`; local project `proyecto/` (packages symlinked to the Chaise project, manifest identical, Mathlib 8f9d9cff).
- Forbidden-construct grep (sorry|admit|axiom|native_decide|implemented_by|unsafe|opaque|extern): none.
- Build: `build_run1.log`, 8029 jobs OK, 178 s, peak 2.33 GB (vigia, cap 3 GB / 15 min).
- Statements and axioms: `check_run1.log` (by `checks/Check1.lean`), 96 s, peak 2.52 GB. `gram_transpose`, `gram_mulVec_famVec` (every m ≥ 1), `sum_E_pencil` ([Fact m.Prime]), `aug_of_mem_K` ([Fact m.Prime], 5 ≤ m, x ∈ K), plus `formV` (induced form on V = A ⧸ K), `formV_mk`, `formV_isSymm`. Axioms: propext, Classical.choice, Quot.sound only.
- Faithfulness audit: `gramUpper`/`gram` match the Setting case by case (same family 2−m / row-or-column; (0,1) k−l; (1,2) k+l; (0,2) k′−l′ = k+l+1; j > j′ by symmetry); `E`, `pencil` (Option: some t = π_t, none = π_∞), `aug`, `restrict`, `famVec` as in the piece. Aristotle's proof of (W1.d) uses G·y mod m only, slopes t = 2, 1, −1 (allowed by the piece). PASS.
- Next: W2 (Lemma C).

## W2 SENT — 29 Sep ~22:15, task f501afa3 (same project 884019b5)
- Piece `pieces/w2_counting_lemma.md`: SAT data, SatSrc (nine sum-zero functions + ε₁, ε₂), satMap over any ring, SAT m over ℤ; (W2.a) finrank; (W2.b) compatibility + lift of sum-zero functions; (W2.c) Lemma C: ker = 12, range = 9m − 19, for m ≥ 5 prime. Proof by mixed second differences (not the paper's polynomial dictionary; same statement).
- **Found while checking:** the (0,2) overlap needs the translation `x ↦ x − 1` (family 2 term `w_2(k − l − 1)`): the only shift with SAT ⊂ K at m = 3, 5, 7, 11 (`checks/w2_sat.py`, `w2_sat.log`). Controls: other shifts and swapped pencils not in K.
- Checks: rank_Q = 9m−7, rank mod m = 9m−19, kernel 12 at m = 5, 7, 11; solving the identities directly gives 12 at m = 5, 7, 11, 13 with quadratic w's of common leading coefficient (`w2_relations.py/.log`); m = 3 gives 11 (control).
- Next after W2 certifies: W3 (census / Lemma P) or W5 (SAT ⊂ K — now easy to state with this satMap).

## W2 CERTIFIED — 29 Sep ~22:45 (run 2, task f501afa3, tarball `…-aristotle (1).tar.gz` md5 c10d5251811346b62fd138b2c56a2144)
- `run2/output-final_aristotle/`; Defs.lean, W1.lean, Main.lean byte-identical to run 1; new `W2.lean` (554 lines) copied into `proyecto/`.
- Grep: none. Build `build_run2.log`: OK, 53 s, peak 2.12 GB. Statements/axioms `check_run2.log` (by `checks/Check2.lean`), peak 2.35 GB: axioms propext, Classical.choice, Quot.sound only.
- Audit PASS: `satFun` = the three family formulas of the piece verbatim (w 2 (k − l − 1) for the (0,2) pair); `SatSrc` = kernel of the nine sums; `SAT m` = image of `SatSrc ℤ m`. Theorems: `finrank_sumZero` (m − 1), `finrank_satSrc` (9m − 7, any field), `satMap_red`, `red_mem_satSrc`, `exists_sumZero_lift`, `exists_satSrc_lift`, **`finrank_ker_satMap` = 12 and `finrank_range_satMap` = 9m − 19 ([Fact m.Prime], 5 ≤ m)**, plus `map_ker_satMap_eq` (kernel = range of an explicit injective 12-parameter map).
- **Error of mine in the piece, caught by Aristotle:** the lift in the proof of (W2.b) subtracted `(Σ y₀)/m` at 0, which does not zero the sum; the right correction subtracts `Σ y₀`. Statement unaffected.

## W3 SENT — 29 Sep ~23:00, task d004cb9e (same project)
- Piece `pieces/w3_sat_in_K.md`: (W3.a) SAT ≤ K for EVERY m ≥ 1 (the paper's «file-verified» step, now with proof: row of G, sum fact S1, parity cancellation S2 — `(x,e) ↦ 2x+e` is exactly 2-to-1); (W3.b) satMap ℤ injective on SatSrc ℤ for odd m ≥ 3 (mixed differences + periodicity over ℤ); (W3.c) finrank ℤ SAT = 9m − 7, odd m ≥ 3.
- **Prediction of mine falsified by my own check:** I expected SAT ⊄ K at even m; it holds at m = 4, 6 too. Injectivity does fail at even m (rank 9m − 8). Checks `checks/w3_sat_in_K.py/.log` (m = 3,4,5,6,7,9,11,15; control non-sum-zero datum not in K).
- Remaining for the final target (paper §§3–6, 8, 10): census / Lemma P, trace-lattice discriminant (Lemma T), transport, big determinant, [SAT:K₀], mK ⊆ SAT (R.3–R.4), assembly. Plan the route before W4: the assembly may be easier via |disc V| = |Tors coker G| (product of the nonzero elementary divisors, verified 5^12, 7^48).

## W3 CERTIFIED — 29 Sep ~23:30 (run 3, task d004cb9e, tarball `…(2).tar.gz` md5 8a6ed828c3f7d8005e8a28f839e6d6a2)
- Defs/W1/W2 byte-identical; `W3.lean` (467 lines) into `proyecto/`. Grep none. Build `build_run3.log` 47 s, 2.08 GB; `check_run3.log` (checks/Check3.lean) 116 s, 2.03 GB. Axioms standard.
- `gram_mulVec_satMap`, **`SAT_le_K` (every m ≥ 1)**, `eq_zero_of_satMap_eq_zero` / `satMap_injOn` (Odd m), **`finrank_SAT = 9m − 7` (Odd m)**, `finrank_satSrc_int`. Audit PASS (hypothesis `Odd m` covers odd m ≥ 3, and m = 1 harmlessly).

## THE LEAN ROUTE (Grepy, 29 Sep ~23:45) — integer, no characters; differs from the paper's §§3–6, same theorem
Let `pb j π u` = pullback of `u : ZMod m → ℤ` along pencil π on family j; `Z₀` = sum-zero functions.
1. **G on pullbacks** (u ∈ Z₀): axis pencils → 0; live non-overlap t ∉ {0, ±1} → `−m·pb`; the six overlap formulas (pencils ±1, pairs (0,1) at −1, (1,2) at +1, (0,2) with shifts u(x∓1)). **W4.**
2. **Census + mK ⊆ SAT** (R.1 + pairing x ∈ K against pb(u)); rank K = 9m − 7 for free; **[K : SAT] = m^12** from Lemma C + K saturated. **W5.**
3. **F** := live non-overlap blocks + lower member of each overlap pair + N₀ (rank 3(m−1)(m−2)+1). `L := F + SAT = ⊕_j L_j`, `L_j = Σ_π pb^π(Z₀) + ℤ·1`, standard Gram block-diagonal ⟹ **[ℤ^P : L_j] = m^{(m²+m+2)/2}**; F ∩ K = 0 ⟹ `[F+K : F+SAT] = [K:SAT]` ⟹ **[A : F+K] = m^{3(m²+m+2)/2 − 12}**. **W6.**
4. **disc B|_F = ±m^{3(m−2)(2m−1)+3}** (blocks −m²·Gram(Z₀) = −m²(I+J), det m^{2m−1} each; N₀ block m³); `disc φ(F) = [V : φ(F)]²·disc V` ⟹ **|disc V| = m^{3(m−3)²}**. **W7.**
Checks (`checks/w4_route.py/.log`, `w4_diag.py`, `w4_idx5.m2/.log`, `w4_idx7.log`): G-formulas at m = 5, 7, 11 (after fixing the (0,2) shift direction in my test); [ℤ^P:L_j] = m^16, m^29, m^67 at m = 5, 7, 11; disc B|_F = 5^84, 7^198; [A : F+K] = 5^36, 7^75; [K : SAT] = 5^12 (7: killed by the vigía at 1.2 GB, not needed). 84 − 72 = 12 = 3·2², 198 − 150 = 48 = 3·4².

## W4 SENT — 29 Sep ~23:55, task b499b938 (same project)
- Piece `pieces/w4_pencil_calculus.md`: `pb`, `fib`; (W4.a) two pencils are independent coordinates; (W4.b) G on pullbacks of sum-zero functions (axis 0, live non-overlap −m, six overlap formulas with the (0,2) shifts u⁻/u⁺); (W4.c) R.1 as a vector identity per family.
- Next: W5 (census, mK ⊆ SAT, [K : SAT] = m^12), W6 (index [A : F+K]), W7 (disc F and assembly). See «THE LEAN ROUTE» above.

## W4 CERTIFIED — 30 Sep ~00:20 (run 4, task b499b938, tarball `…(3).tar.gz` md5 f1aa3d2c9f1253924148a20be8dfdbe3)
- Defs/W1–W3 byte-identical; `W4.lean` (355 lines). Grep none. Build `build_run4.log` 51 s, 2.17 GB; `check_run4.log` (checks/Check4.lean) 92 s, 2.48 GB; axioms standard.
- `pb`, `fib`, `ext` as in the piece. `sum_pencil_mul_pencil` (prime), `sum_pencil_mul_same` (any m), axis formulas (any m), `gram_mulVec_pb_live` (prime, t ∉ {0,±1}), six overlap formulas (Odd m; (0,2) with u(x−1), u(x+1) exactly), `smul_ext_eq_sum_pb_fib` (prime). Audit PASS.

## W5 SENT — 30 Sep ~00:35, task 2aa54b1f (same project)
- Piece `pieces/w5_mK_in_SAT.md`: (W5.a) census (live fibre sums constant; overlap differences constant, (0,2) with shift v+1); (W5.b) m•x ∈ SAT for x ∈ K (explicit datum: a_j, b_j axis fibres, w_0 = f̃_{0,−1}, w_1 = f̃_{1,1}, w_2 = f̃_{0,1}, ε₁ = μ₀, ε₂ = −μ₂); (W5.c) finrank K = 9m − 7; (W5.d) [K : SAT] = m^12 via K ∩ mA = mK + Lemma C.
- Checks `checks/w5_mK_in_SAT.py/.log`: census and construction exact on all 38 / 56 basis vectors of ker G (M2) at m = 5, 7. Note: `checks/kerG7.txt` is 118 MB (M2 kernel basis, huge entries) — do not ship it to GitHub.
- W6 DRAFTED (not sent; send after W5 certifies): `pieces/w6_index.md` — F, its B-Gram (orthogonal blocks −m²⟨u,v⟩, N₀ ↦ m³), F ⊓ K = ⊥, finrank F = 3(m−1)(m−2)+1, [ℤ^P : Lfam] = m^{(m²+m+2)/2}, F + SAT = L, [A : F+K] = m^{3(m²+m+2)/2 − 12}. Check `checks/w6_index.py/.log`: [A : F+SAT] = 5^48, 7^87 exact.

## W5 CERTIFIED — 30 Sep (run 5, task 2aa54b1f, tarball `…(5).tar.gz` md5 c9168c9c2f243b86204c7c05b5d5e8b8; note `…(4)` was a premature download of the W4 state, unused)
- Defs/W1–W4 byte-identical; `W5.lean` (413 lines). Grep none. Build `build_run5.log` 76 s, 1.64 GB; `check_run5.log` (checks/Check5.lean) 138 s, 1.70 GB; axioms standard.
- `fib_live_const` (prime), `fib_overlap_zero_one/one_two/zero_two` (prime, 5 ≤ m; the (0,2) with v + 1), **`smul_mem_SAT`** (witness `W5.satD`, `satMap_satD = m • x`), **`finrank_K = 9m − 7`**, **`index_SAT`: [K : SAT] = m^12**. Audit PASS.

## W6 SENT — 30 Sep, task cdf7f149 (same project). W7 DRAFTED (send after W6 certifies)
- W6 = `pieces/w6_index.md` (names of W5 results updated: `finrank_K`, `index_SAT`).
- W7 = `pieces/w7_discriminant.md`: the final theorem, **for every ℤ-basis b of V m, det(toMatrix b formV) = m^(3(m−3)²)** (exact, positive), with Module.Free and finrank V = 3(m−1)(m−2)+1. Proof: V free; φ(F) ⊆ V of index [A : F+K]; Gram_c = Pᵀ Gram_b P; det Gram_c = +m^{3(m−2)(2m−1)+3}; arithmetic. Sign checked: `checks/w7_sign.py/.log` gives +5^84, +7^198.

## W6 CERTIFIED — 30 Sep (run 6, task cdf7f149, tarball `…(6).tar.gz` md5 1eb51b50666c555b0aee4d90ddffe0ea)
- Defs/W1–W5 byte-identical; `W6.lean` (802 lines). Grep none. Build `build_run6.log` 64 s, 1.81 GB; `check_run6.log` (checks/Check6.lean) 124 s, 1.85 GB; axioms standard.
- `blk`, `LiveT`, `FIdx` (inl (j,t) = blk j (some t), inr 0/1/2 = blk 0 (−1), blk 1 (1), blk 0 (1)), `F`, `Lfam`, `L` as in the piece. `gramForm_pb_pb_of_ne`, `gramForm_famVec_pb`, `gramForm_pb_pb_self` (−m² Σuv), `gramForm_famVec_self` (m³), `F_inf_K`, `finrank_F`, `index_Lfam` (every prime), `F_sup_SAT`, `index_F_sup_SAT`, **`index_F_sup_K = m^(3(m²+m+2)/2 − 12)`**. Audit PASS.

## W7 SENT — 30 Sep, task c097cb76 (same project): the final theorem `watermark_theorem` (Module.Free, finrank V = 3(m−1)(m−2)+1, det(toMatrix b formV) = m^(3(m−3)²) for every ℤ-basis b). Piece `pieces/w7_discriminant.md` (names of W6 results updated).

## STATE AT 30 Sep (saved before compacting) — Rafa says W7 FINISHED; certify it on return
1. Chrome tab 585561209 → reload the project page; confirm W7 properties present and no RUNNING; JS click `button[aria-label="Download project"]` (only after confirming — a premature click downloads the previous state, as happened with W5).
2. Newest `~/Downloads/884019b5-…-aristotle (N).tar.gz` → extract to `run7/`; summary; cmp Defs, W1–W6 against `proyecto/`; grep forbidden; manifest identical.
3. Copy `W7.lean` into `proyecto/RequestProject/Watermark/`; build `lake build RequestProject.Watermark.W7` inside vigia (TOPE_KB=3145728 TOPE_S=900), log `build_run7.log`.
4. `checks/Check7.lean`: `#check @Watermark.watermark_theorem`, `#print axioms`; also a full `lake build` of the project; audit the statement against `pieces/w7_discriminant.md` (Module.Free ℤ (V m); finrank V = 3(m−1)(m−2)+1; ∀ basis b, det (LinearMap.BilinForm.toMatrix b (formV m)) = m^(3(m−3)^2); hypotheses m prime, 5 ≤ m only).
5. If PASS: THE WATERMARK IS CERTIFIED IN LEAN — record here, CLAUDE.md, arbol.yaml (new node, meta.version 296, backup first), memory, LISTA_DE_PENDIENTES; copy tarball (7) into `CHAISE_LONGUE_COPIAS_DE_FUERA_2026-09-30/DESCARGAS_TARBALLS_ARISTOTLE/` and refresh the manifest. Then plan with Rafa: Watermark certificate + v2 paper (new integer proof), cold read, Zenodo/ORCID, GitHub; Double Ladder by pencil.

## W7 CERTIFIED — 30 Sep ~07:10 (run 7, task c097cb76, tarball `…(7).tar.gz` md5 c0b960aa8bb14fa05ad2fc2f8d703bb4) — THE WATERMARK THEOREM IS CERTIFIED IN LEAN
- Reloaded first: task complete, nothing RUNNING, then downloaded. Defs/W1–W6 and lakefile/toolchain/manifest byte-identical; `W7.lean` (249 lines). Grep none.
- Build `build_run7.log` 89 s, 1.37 GB; `check_run7.log` (checks/Check7.lean) 139 s, 1.59 GB.
- `watermark_theorem [Fact m.Prime] (hm : 5 ≤ m)`: `Module.Free ℤ (V m)` ∧ `finrank ℤ (V m) = 3(m−1)(m−2)+1` ∧ ∀ ℤ-basis `b` (any finite index type), `det (toMatrix b (formV m)) = m^(3(m−3)^2)`. Also `V_free` (any m ≥ 1), `finrank_V`. Axioms: propext, Classical.choice, Quot.sound. Audit against `pieces/w7_discriminant.md`: PASS.
- Tarball copied to `CHAISE_LONGUE_COPIAS_DE_FUERA_2026-09-30/DESCARGAS_TARBALLS_ARISTOTLE/` (manifest updated). Tree v296.
- Next, with Rafa: Watermark Lean certificate + v2 paper (integer proof; SAT ⊂ K as a theorem), cold read, Zenodo/ORCID, GitHub; Double Ladder by pencil.

## LEAN CERTIFICATE WRITTEN — 30 Sep ~08:05
- `LEAN_CERTIFICATE_WATERMARK_v1.md` (md5 f913002d…) + `.pdf` (13 pages, md5 90aaadd5…) + `.html`, converter `corpus4/herramientas_grepy/regla289_watermark_cert_md2html.py`.
- New evidence produced for it: `checks/CheckFinal.lean` (#print of all 11 definitions; non-vacuity at m = 5 proved in Lean) → `checkfinal.log`, `checkfinal_fresh.log`; `checks/DepsFinal.lean` → `deps_watermark.log` (410 declarations, 8 files); `checks/wfinal_geometry.py/.log` (Lean G = geometric intersection matrix at m = 5, 7, 11; control fails); `checks/w4_formulas_recheck.py/.log`; clean rebuild module by module `clean_rebuild_2026-09-30.log` + `cr_*.log` (9/9, 11 min 05 s). Old build dir moved to `_BORRAR/LAKE_BUILD_WATERMARK_ANTES_DE_LIMPIA_2026-09-30`.
- Next: cold read of the certificate; Watermark paper v2; Double Ladder decision (glue test at m = 5, 7, 11).

## STATE AT 30 Sep ~08:20 (saved before compacting #2) — RAFA'S ORDER, IN THIS ORDER
Done today: W7 certified; Lean certificate v1 written (md+pdf, 13 pp); tree v297. Nothing running.
**Step 2 (next): close the Double Ladder by pencil if possible, and send DL1 to Aristotle.**
- Source, highest version (md5 checked on the whole Mac): `corpus/THE_DOUBLE_LADDER_THEOREM_v2.md` md5 `7b10b75ddffc55eed020c424f72590ef` (117 lines) = repo `hodge-fermat-campaign/THE_DOUBLE_LADDER_THEOREM.md`. Statement: for prime m ≥ 7, `V*/V ≅ (Z/m)^{3m²−24m+59} × (Z/m²)^{3m−16}`; m = 5: `(Z/5)^{10} × Z/25`. Anchors: m = 5, 7 (AMV rows), m = 11 sealed `(Z/11)^{158} × (Z/121)^{17}`. Status (its own remark + pendientes XII item 89): four steps verified at 3–4 primes, NOT proved for every prime; it rests on the paper's character route (flat law, glue law, cap, determinant 6 of nine «shadow» classes, rank ladder `rank(Q|𝔪^K) = 12(m−3) − 3K(K+1)`), none of it in Lean.
- **Idea to test first (integer route, same objects as W6–W7):** `F ⊆ V ⊆ V* ⊆ F*`, so `V*/V ≅ H^⊥/H` with `H = V/φ(F) ≅ A/(F+K)` (order `m^{3(m²+m+2)/2 − 12}`, W6). `F*/F` is explicit: each block `−m²(I+J)` on `Z₀ ≅ Z^{m−1}` has Smith form `(m²,…,m², m³)` (check), `N₀` gives `Z/m³`. Compute H inside F*/F at m = 5, 7, 11 and compare `H^⊥/H` with the three profiles; if the structure is readable with m as a letter, write DL1 (e.g. the exponent of V*/V divides m², or F*/F and the glue map) and send it.
**Step 3 (while Aristotle works on DL1): odd composite m.** Test `disc` of the line lattice at m = 9, 15, 21, 25 (expected `m^{3(m−3)²}`, SSvL checked odd m ≤ 81) and whether it splits by the order of characters. Clues to read BEFORE computing: `hodge-fermat-campaign/THE_BLOCK_DECOMPOSITION.md` (CRT block split, per-block rank law), `THE_LOCALIZATION_THEOREM.md` (torsion localized to one CRT block, PROVED), `THE_WATERMARK_LAW.md` (the empirical law for every degree, 12/12 + 5 blind; its §0 says **Shioda's 1987 conjecture was for PRIME degree** — if confirmed in [Sh], the Watermark closes Shioda's conjecture entirely and composites are our own Watermark Law), and the Chaise v8 §6 colour reduction (composite key). Rafa offers a metaphor if needed.
**Step 4 done:** standby handoff `GREPY_EN_ESPERA_v1.md` (root).

# ESTADO — Double Ladder (pencil proof and Lean), live state, newest block last

## 30 Sep 2026 — PENCIL PROOF FOUND; DL1 SENT
- Source statement: `corpus/THE_DOUBLE_LADDER_THEOREM_v2.md` (md5 7b10b75d…, highest version, checked on the whole Mac).
- **Pencil proof:** `THE_DOUBLE_LADDER_PENCIL_PROOF_v1.md` (this folder). Three facts:
  1. the order `m^{3(m−3)²}` (Watermark, in Lean);
  2. the exponent divides `m²`, from `G Y G = 6m² G` with `Y = ⊕_j (P_k + P_l + 3P_{k−l} + 3P_{k+l}) − 6m I`, proved on the W4 pieces;
  3. `rank(G mod m) = 12(m−3)` for `m ≥ 7` (shadow factorization `G = SᵀΓS − mI`, moments of degree ≤ 2, `Σ_{x∈F_m} x^s = 0` for `s ≤ m−2`), and `26` at `m = 5`.
  Assembly: `n₂ = 3m − 16`, `n₁ = 3m² − 24m + 59`.
- Checks `checks/dl_*.py/.log`: the certificate holds exactly at m = 5, 7, 11, 13, 17, with controls; the Smith profiles at 5, 7, 11, 13 match, and **m = 13 is a new cell, (Z/13)^254 × (Z/169)^23**; every intermediate step is checked.
  > 🔴 **NOTE `2026-09-30` (Grepy):** false. `m = 13` is row `(2,13)` of Table 1 of Aljovin–Movasati–Villaflor (2019), read in the original; AMV also lists `m = 5, 7, 11`.
- **DL1 SENT** to Aristotle, Watermark project 884019b5, **task `4bc5652a`**: piece `pieces/dl1_exponent.md` (ylad, (DL1.a) GYG = 6m²G, (DL1.b) ∃X, M·X = m²·1 for every basis, (DL1.c) m²V* ⊆ V welcome). Target file `RequestProject/DoubleLadder/DL1.lean`.
- Next pieces:
  - **DL2:** rank of G mod m = 12(m−3), m ≥ 7 (§3), plus the m = 5 case if feasible;
  - **DL3:** the assembly, via Mathlib's Smith normal form / `Submodule.quotientEquivPiZMod` (§4).
- Certification cycle as for the Watermark (`GREPY_EN_ESPERA_v1.md` §4).

## 30 Sep — DL1 CERTIFIED; DL2 SENT
- **DL1 CERTIFIED** (run 1, task 4bc5652a, tarball `…aristotle (8).tar.gz` md5 42ae52ff42b470a9575e298b33d81632). Reloaded first: task complete, nothing IN PROGRESS. Defs, W1–W7, Main, lakefile/toolchain/manifest byte-identical; `DL1.lean` 394 lines; grep clean. Local build 65 s, peak 1.59 GB (`build_run1.log`). `checks_lean/CheckDL1.lean`: statements printed, identical to the piece; `ylad` printed, as written; axioms [propext, Classical.choice, Quot.sound] (`check_run1.log`).
  - `DoubleLadder.gram_mul_ylad_mul_gram` (m prime, 5 ≤ m): G·Y·G = 6m²·G.
  - `DoubleLadder.exists_toMatrix_mul_eq`: ∀ basis b, ∃ X, M·X = m²·1.
  - `DoubleLadder.exists_formV_eq_smul`: m²·V* ⊆ V.
- **DL2 SENT, task f130f94c**: piece `pieces/dl2_rank_mod_m.md` (pen4, shadow, gam, relMap; (DL2.a) G = SᵀΓS − mI; (DL2.b) ker relMap = span of 6 relations; (DL2.c) quadratic pairings vanish for m ≥ 7; (DL2.main) rank(G mod m) = 12(m−3); (DL2.basis); (DL2.five) welcome). Checks `checks/dl2_checks.py`.
- **Probe on odd composites** (`checks/comp_probe.py/.log`, m = 9, 15, 21, 25): the minimal polynomial x(x+m)(x+2m)(x−3m) and G·Y·G = 6m²·G hold for every one; rank K = 9m − 7; disc of the line lattice = m^{3(m−3)²} (the Watermark law, as SSvL found), exponent m². p-parts: m=15: 3-part (Z/3)^360×(Z/9)^36, 5-part (Z/5)^370×(Z/25)^31; m=21: 3-part b=54, 7-part b=47; m=9: valuations up to 4 at 3; m=25: up to 4 at 5.
- Next piece: **DL3** (assembly via Smith normal form), to write after DL2 certifies.

## 30 Sep — DL2 CERTIFIED (general part; m = 5 build pending); DL3 SENT
- Run 2 (task f130f94c, tarball `…aristotle (9).tar.gz` md5 429bc68553cb2ddc6e1b4550f391d400). The task was complete, with 0 IN PROGRESS. Defs, W1–W7, DL1, Main and lakefile/toolchain/manifest are byte-identical. `DL2.lean` has 774 lines. The grep is clean except for `decide +kernel` at lines 741 and 757, which are the m = 5 certificates only (kernel evaluation, not native_decide).
- **Full local build KILLED by the watchdog at 901 s**, peak 2.37 GB (`build_run2.log`): the m = 5 kernel evaluation (75×75 matrices over ZMod 5) is slow on this Mac. Aristotle reported about 2 minutes on its side.
- **General part CERTIFIED locally:** `checks_lean/DL2_general_only.lean` is Aristotle's file verbatim up to `namespace DL2.Five`, with the `module` header removed so that `#print axioms` works. It compiles with no errors, 149 s, peak 1.96 GB. Axioms [propext, Classical.choice, Quot.sound] for `gram_eq_shadow`, `ker_relMap_eq_span`, `finrank_ker_relMap`, `sum_mul_shift_eq_zero`, `rank_gram_map` (m prime ≥ 7: rank(G mod m) = 12(m−3)) and `rank_toMatrix_map` (`check_run2_general.log`). The statements match the piece.
- **Pending:** the local build of the m = 5 part (`rank_gram_map_five`). It needs a time limit above 15 min, with memory under 3 GB, and **Rafa's authorization**.
- **DL3 SENT, task 24f74a8c**: piece `pieces/dl3_assembly.md` (D m := Dual/range formV; `double_ladder_theorem` (m ≥ 7) and `(DL3.five)`; DL3.group welcome; asked to avoid heavy decide).
- **30 Sep: RAFA AUTHORIZED ONE 45-MINUTE LEAN BUILD** (memory cap 3 GB) for the full DL2 including m = 5; running now, log `build_run2_full.log`.
- **30 Sep: Rafa extended it to «lo que haga falta».** The 45-min run was stopped after 1.5 min (`build_run2_full_aborted45.log`) and relaunched with a 4-hour time cap and the 3 GB memory cap, log `build_run2_full.log`.

## 30 Sep — DL3 DOWNLOADED AND AUDITED; LOCAL BUILD WAITS FOR THE DL2 OLEAN
- Run 3 (task 24f74a8c). Reloaded first: task complete, «Aristotle finished successfully», IN PROGRESS 0; 44 properties proved. Tarball `…aristotle (10).tar.gz` md5 11b808fe1cc958bbf31be3a0a1663d96, extracted to `run3/`, copied to the COPIAS folder and appended to its manifest.
- Defs, W1–W7, DL1, DL2, Main, lakefile/toolchain/manifest byte-identical. `DL3.lean` 415 lines, md5 e1a3cfa3…; grep for sorry/admit/axiom/native_decide/implemented_by/extern/unsafe/opaque/decide: **nothing** (DL3 has no kernel evaluation of its own).
- Statements read in the file, identical to the piece:
  - `DoubleLadder.double_ladder_theorem (m) [Fact m.Prime] (hm : 7 ≤ m) : Nonempty (D m ≃+ ((Fin (3*m^2+59−24*m) → ZMod m) × (Fin (3*m−16) → ZMod (m^2))))`;
  - `DoubleLadder.double_ladder_five : Nonempty (D 5 ≃+ ((Fin 10 → ZMod 5) × ZMod 25))` (uses DL2's `rank_gram_map_five`, i.e. the `decide +kernel` certificates);
  - `DoubleLadder.equiv_of_card` (DL3.group), with the three hypotheses and `c ≤ N ∧ N ≤ 2c` as asked;
  - `D m := Module.Dual ℤ (V m) ⧸ LinearMap.range (formV m)`, as specified.
- Proof route as in the piece: `discrEquiv` (D ≅ ℤ^ι/range M via `b.constr`), `card_coker` (order = |det|, `Submodule.natAbs_det_equiv`), `sq_smul_discr_eq_zero` (DL1), `card_coker_quot_smul` (D/mD has m^{r − rank M̄} elements), `discr_equiv_of_rank`, arithmetic by `m = n + 7`.
- DL3.lean copied into the local project. **Local build and `checks_lean/CheckDL3.lean` pending: DL3 imports DL2, whose full build (with the m = 5 kernel certificates) is still running in the watchdog** (`build_run2_full.log`, 4 h cap). One heavy run at a time.

## 30 Sep — THE DOUBLE LADDER THEOREM CERTIFIED IN LEAN
- **Why the full DL2 build never finished:** each m = 5 certificate (`hBC`: Ḡ = B·C, 75 rows; `hXY`: 26 rows of Ḡ times Y = 1) was ONE `decide +kernel` theorem. The kernel cache grows within a declaration: 1 row costs +2 s and nothing in memory; 25 rows in one theorem cost +49 s and +1 GB (`test5_*.log`). Whole: ~9 GB real footprint on an 8 GB Mac ⟹ swap, 6.5 min of CPU in 50 min. Aristotle has plenty of RAM. The run was stopped on Rafa's order.
- **The watchdog was blind to it:** `vigia.sh` v2 measured RSS only (0.6 GB shown, 9 GB real). v3 measures max(RSS, phys_footprint). Honest baseline: loading Mathlib ≈ 3 GB.
- **Fix:** `hBC` split into 15 lemmas `hBC_j_a` (per (j,a)) and `hXY` into 26 lemmas `hXY_i` (per row), still `decide +kernel`, then assembled by `ext`/`fin_cases`. Statements of `hBC`, `hXY`, `rank_gram_map_five`, the whole general part and the final theorem are byte-identical to Aristotle's (`DL2_split_m5.diff`; Aristotle's original kept in `run2/`). Local DL2.lean md5 2c9a0d718bc28c7bb9de99bc0582a9e4.
- **DL2 full (m = 5 included): 81 s, peak 4.15 GB. DL3: 23 s.** Clean rebuild from scratch of all 11 modules: 333 s, peak 4.14 GB (`build_clean_all.log`).
- `checks_lean/CheckDL3.lean` (`check_run3.log`, repeated after the clean build in `check_run3_clean.log`): statements printed, identical to the piece; **axioms [propext, Classical.choice, Quot.sound]** for `double_ladder_theorem`, `double_ladder_five`, `equiv_of_card`.
- Next with Rafa: Lean certificate of the Double Ladder (md + pdf), cold read, then items 111–113 of the pending list.

## 30 Sep — LEAN CERTIFICATE WRITTEN; PRIORITY READ; v3 ON GITHUB
- Certificate `LEAN_CERTIFICATE_DOUBLE_LADDER_v1.md/.html/.pdf` (11 pages, built with `corpus4/herramientas_grepy/regla290_cert_md2html.py` + Chrome headless).
- `checks_lean/CheckDLFinal.lean`: exit 0, 99 s, 2.20 GB (`checkdlfinal.log`): statements, `D`, `ylad`, axioms standard, non-vacuity at m = 7, 11, 13. `checks_lean/DepsDL.lean`: cone 609 (m ≥ 7) / 632 (m = 5) declarations in 11 files (`deps_dl.log`).
- Priority read in the original (Shioda 1987 and 2015, SSvL, Degtyarev, AMV, Jumagulov): see certificate §9. AMV Table 1 already had m = 5, 7, 11, 13.
- `corpus/THE_DOUBLE_LADDER_THEOREM_v3.md/.pdf` uploaded to both GitHub repos (Rafa's order), verified by git hash.

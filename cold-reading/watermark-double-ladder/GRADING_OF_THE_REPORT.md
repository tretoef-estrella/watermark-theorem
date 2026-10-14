# Grading of the cold reading «Grepy la Filigrana» (REPORT_WM_DL_1.md, md5 42329744020b3ac15ec55d4e29ece355)

Graded by Grepy el Notario, Wed Oct 14 09:15:59 CEST 2026.

**Mark: HIGH.** Verdict accepted: HOLDS WITH CORRECTIONS (FATAL 0, GAP 0, ERROR 2, PRESENTATION 21).
Every row is a derivation, not a stamp. Its engines (checks/) are its own; C1–C5 controls fail as they must.

## Each item, checked by the auditor before applying
- E-1 (Lemma 14 lift): correct. y − (Σy)δ_0 has sum 0 and differs from y at 0 by Σy ≡ 0 mod m. Applied.
- E-2 (§11 SSvL bullet): correct; SSvL computed the Gram determinant of their basis 𝓑. Applied with its replacement.
- P-1: 2775/10731/65703 = n(n−1)/2 for n = 75, 147, 363 (recomputed). Applied.
- P-2, P-3, P-4 (and Remark 29 to match), P-6, P-7, P-9, P-10 (also the «Lean» paragraph of §1), P-11, P-12, P-13, P-14, P-15, P-16, P-17, P-19, P-20, P-21: applied.
- P-5: the 3-line hand proof re-derived by the auditor (only the three degree-2 relations pair; diagonal 8Σx⁴, off-diagonal Σx⁴; Σ_{F_5}x⁴ = 4 ≡ −1; −(7I+J) ≡ 3I+4J mod 5, eigenvalues 3,3,0, rank 2). Applied.
- P-8: AMV arXiv v2 Table 1 row (2,7) prints «−1^48·7^38·49^5» — confirmed by the auditor with pdftotext. Footnote added.
- P-18: Use of AI reworded truthfully (one reading; corrections applied without a second reading — Rafa's decision of 14 Oct).
- Extra (not in the report): datum letter D renamed Θ (D is also V*/V); Lemma 12 injectivity now names ε₁, ε₂; Prop. 5 families 0/2 says x₃ ≠ 0; Sh15 bullet says «for every m prime to 6; proved here for prime m only» (reader's optional L2 note); WMEven title as on Zenodo.

Script: ../edits/apply_filigrana.py (anchored, every replacement asserted once).
Result: tex md5 1c0c9adf06cc16bd87a110807ef22ade, pdf md5 82be2a1ddfd91c7a37a91371feb8b2ba, 12 pages, 0 errors, 0 undefined references, 18 \bibitem, one 0.8 pt overfull box (invisible). Every page looked at (build/png_fil).
No second cold reading (Rafa: «no es necesario un lector en frío para esto»).

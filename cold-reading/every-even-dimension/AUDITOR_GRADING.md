# Cold reading of «The Watermark in Every Even Dimension», v2 — the auditor's grading

1 October 2026. Reader: one independent AI session (Claude), launched with Rafa's authorization («lanza la lectura en frío»), working only in `~/Desktop/LECTORES_EN_FRIO/WATERMARK_THM_1/`. Report: `REPORT.md` (md5 `4350ea56ab2848978cb3731c9729f538`), scripts and logs in `cold/`. The text it read: `NOTE_AS_READ_BY_THE_COLD_READER.md`; the text just before the findings were applied: `NOTE_BEFORE_APPLYING_THE_FINDINGS.md`.

## Verdict of the reader
**HOLDS WITH CORRECTIONS.** No fatal error. 4 errors of statement (F1–F4), 3 small gaps (F5–F7), 13 points of presentation (F8–F20).

## Grade: HIGHEST MARK
- It re-derived every proof line by line and wrote four engines of its own (lattice, deltas, points, ring).
- F1 is a real error of mine: «the eigenline of `a` has type (k,k) exactly when `a ∈ 𝔅`» is false (`m = 5`, `a = (1,3,3,3)`); the conclusion (1) was right, but its second half was not argued at all.
- F3 is right: I wrote «Theorem 1 is proved twice» when (ii) and (iii) use Theorem 1. The repaired statement is the equality of orders only.
- F4 is right and important: the polynomial table interpolates the walk statistic, not the formula of Theorem 3, outside the 22 cells where the ring was computed.
- It went beyond the mandate: Theorem 1 and Remark (ii) at five composite cells against [AMV, Table 1] with all the elementary divisors, by a method (prime by prime, from indices) that runs in seconds where my integer Hermite reduction blew up.
- It found a shorter proof of `δ_Y` in Theorem 4 (F18).
- It declared what it could not verify, and its five runs killed by the guard.

## What was done with each finding
| finding | action |
|---|---|
| F1 | §1.3 rewritten: Hodge type by [SK]; proof of both halves of (1) |
| F2 | Problem 2 corrected (ranks 86 and 62 at (2,6)) |
| F3 | Remark after Theorem 2 rewritten (second proof of the equality of orders only) |
| F4 | §6, Conjecture P and §10 say what was interpolated (walk statistic; formula of Theorem 3 in the cells of Table 6) |
| F5 | proof of Theorem 4 completed (stabilizer, rank, degree-1 class, pure power of p) |
| F6 | Remark (ii) completed (stabilizers, [DS, Thm 1.4], even m, [Deg], [DS, §5]) |
| F7 | second inequality added to Theorem 3(a), with its proof |
| F8 | §10 paragraph written |
| F9 | [ABB] cited (I had found it independently while the reader was working; read in the arXiv pdf) |
| F10 | «every published computation for prime degree known to us»; [SSvL] cited as in [WDL] |
| F11 | Table 4 bis added; the reader's engine was run again by me (logs `grupolector_*.log`) |
| F12 | `Q_k(p)` defined |
| F13 | Lemma 3.3 hypothesis fixed |
| F14 | Remark (tangent cone) added; «modulo `x_0^{p−1}`» |
| F15 | notation of §4 fixed |
| F16 | «as an algebraic group, over an infinite field» |
| F17 | §10 lists the inputs, what was read in the original, the unrefereed inputs |
| F18 | Remark after Theorem 4 |
| F19 | sentence on the predictions of version 1 removed |
| F20 | (a) simplified; (b) said; (c) count fixed; (d) captions kept with tables; (e) said; (f) fixed |

## Added after the reading (not read cold; said in §10 of the note)
Engine 7 and Table 5 (the lattices built from Looijenga's form: `|disc H°| = p`, the rows (6,3) and (8,3) of [AMV, Table 2]); the rewriting of the open problems as Conjectures P and S, with `conos_tangentes_A_T.log` (13 cells).

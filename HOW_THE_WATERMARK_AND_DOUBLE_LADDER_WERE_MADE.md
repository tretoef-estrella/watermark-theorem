# How the Watermark and Double Ladder Theorems Were Made

### The story, the method, and who did what

**Rafael Amichis Luengo** · Madrid · 30 October 2026

*A note on how the Watermark and Double Ladder theorems were found and proved, and on the way of working behind them. To write it we went through every conversation and working document of the project. The text was written by Claude from my general indications (see the note at the end), and every date, name and quotation in it was checked against those records, which are kept in full.*

---

## In one page

**What was proved.** For the complex Fermat surface `S_p` of prime degree `p ≥ 5`, the discriminant of the Néron–Severi lattice is `p^{3(p−3)^2}` (the Watermark Theorem), and the discriminant group is `(Z/p)^{3p^2−24p+59} × (Z/p^2)^{3p−16}` for `p ≥ 7`, `(Z/5)^{10} × Z/25` for `p = 5` (the Double Ladder Theorem). The first answers formula (7.10) of Shioda's Question 7.4 (1987).

**When.** The formula and the first proofs came in two days, 4 and 5 June 2026. The proofs in the paper were written on 30 September 2026, when both lattice statements were also checked in Lean 4. The paper was assembled on 14 October.

**Who.** I directed the work. I chose what to pursue and what to drop, I asked the questions, and I gave images when the work was stuck. The mathematics was done by instances of Claude (Anthropic): one instance built, a separate instance audited, and further independent instances read the finished texts cold. The Lean proofs were written by Aristotle (Harmonic) and compiled and checked on my own laptop. No human mathematician took part in the work.

**How it can be trusted.** Not because an AI wrote it, and not because I say so. Four things carry the weight: (1) the builder never audited his own work; (2) every number was recomputed by the auditor with his own code, and predictions were written down before the computations that could refute them; (3) every claim of novelty was checked against the published sources, read in the original, and three of our own claims were withdrawn or narrowed that way; (4) the lattice statements are checked by the Lean kernel, and what Lean does not check is said in the paper. The full record, including the dead ends, is kept and can be inspected.

---

## 1. Where it started

I trained in psychology, not mathematics. I think in images. In May 2026 I started a campaign on Fermat varieties with Claude: we checked the integral Hodge conjecture cell by cell with the Degtyarev–Shimada criterion, on an 8 GB laptop, running the criterion further than the published table. The campaign began on 23 May. On 3 June an auditor joined the builder and me.

By the morning of 4 June the campaign had hit a wall. Every proof of the absence of torsion we could see was equivalent to Conjecture 1.2 itself, and checking more cells by machine told us nothing new. I wrote to the auditor that morning that there was no innovation left within our reach, that I would try once more with a fresh Claude, and that if he found nothing, the work on Fermat varieties was finished.

The auditor wrote a neutral handover, with no suggestions, for a new builder instance. The rules were: no machine runs, no hunt for counterexamples, only something we had not seen. The new builder read everything and answered: *there is nothing.*

That is where the Watermark comes from.

## 2. 4 June 2026: the Watermark

**A pressure test.** I did not take that answer as the last word. I told the builder that I had an intuition I could not get rid of, and gave him an image:

> «a las cisternas de mercancías peligrosas se les somete a pruebas hidráulicas y neumáticas, y si hay la más mínima grieta, se sabe, aunque sea atómica. No hace falta meterse dentro con un estetoscopio […]» *(my words, accents added)*

Tankers of dangerous goods are tested with water and air pressure, and the smallest crack shows; nobody has to climb inside with a stethoscope. If nothing is cracked, the whole must weigh exactly X.

The builder answered that this test exists for surfaces. The weight is the discriminant. If the lines generate the lattice, the determinant of their intersection matrix takes a known value. He built the gauge the same morning: the Gram matrix of the linear cycles and its Smith normal form.

**The first number dies.** The gauge worked, and it produced a number we thought was new. The auditor checked the literature before accepting it. The number was already in Table 1 of Aljovin, Movasati and Villaflor, and their Algorithm 1 is the same method. The claim was withdrawn at once and written into the project's record of dead routes. The same check showed that three of our own documents said these authors had left the elementary divisors uncomputed. That was false, and the three documents were corrected that day.

**Squeeze the published tables.** What was left was a validated instrument and the published tables. I asked for the tables to be squeezed harder than anyone had squeezed them, by hand, with no new machine runs. Two laws came out: for prime degree `d` the exponent of the discriminant is `3(d−3)^2`; for degree `2q` there is another law, with an unexplained gap of 6 between the two.

**Loose parts.** I said that I could smell something big hiding, not in one piece but split into loose parts so that nobody would catch it. The builder looked, and it was one law: `|disc| = m^{3(m−3)^2}`, with an extra factor `(m/4)^3` when `m` is even. It fits the twelve published rows at once. The gap of 6 is that cube, split between two primes. Before computing anything further, we wrote down the predicted exponents for five degrees beyond the table, seven numbers in all, and sealed them; all seven were then hit exactly. (For the odd ones, Schütt, Shioda and van Luijk had already computed the determinant, as we found afterwards.)

**Whose question it is.** Only then did we read Shioda's 1987 paper. The formula for prime degree is his Question 7.4. Schütt, Shioda and van Luijk had checked it by computer for every odd degree up to 81, and (as we confirmed later in the originals) in 2015 Shioda still used it as expected, not proved. So the prime-degree formula is Shioda's. Ours was, at most, the half he did not state (even degree), which is still a conjecture and is not in the paper.

**The name.** I chose both names with Claude's advice, each for its mechanism. For this one I asked the auditor what the law really does. He explained it and offered four names, with *Watermark* as his favourite, and I chose it. The mechanism behind the name: in the discriminant only one prime appears, the degree itself, and its exponent `3(p−3)^2` depends on the degree alone. The degree is stamped on the lattice like a watermark, which shows only when the whole sheet is held against the light, that is, when the lattice is judged whole, through one number.

**The proof.** Then I asked the auditor for a proof of the odd prime case. He wrote the commission for the builder, called *two lemmas and nothing else*, with a rule I keep: no theorem header until there are zero gaps. The proof was then built step by step through the afternoon. When the builder was stuck I gave him a game. In one, he had to bite a bone without letting go and pin a badge on each piece saying *even* or *odd*. In another, he had to unify even and odd in a single open-handed slap; then came one slap with each hand, and then shaking a wrung towel against a tree until the residue falls out. Each game became a step: a lemma on traces; the reduction of the whole theorem to one index of saturation; the nine blocks of the kernel, each saturating at a known index; and a residue lemma for what is left. In the evening the complete text went to the auditor, who read it line by line. The odd prime half was recorded as proved that night.

**What I contributed that day:** the pressure-test idea, which gave the method; the order to squeeze the published tables rather than compute more; the conviction that two laws were one; wanting to keep going when the fresh builder said there was nothing; the choice of the name; and the images that unblocked each step. The formula as a question is Shioda's; the method and the tables are Aljovin–Movasati–Villaflor's; generation by lines is Degtyarev's and Schütt–Shioda–van Luijk's; the proofs are Claude's.

## 3. 5 June 2026: the Double Ladder

In the early morning I set the plan with the auditor. There were three targets: the whole discriminant group, not only its order; a lattice one dimension higher; and one theorem for all Fermat surfaces. We started with the first, the easiest, on the principle that the hard ones get easier once the first ones fall.

The auditor wrote the commission, and I told it to the builder as a story: a lift going up to the top of a tower, where the builder had to read the floor marker; from the rooftop, nine figures to be found along the balustrade; the lift timed on the way down; and at the bottom, an autograph session: the figures had to lift their shirts so that the builder could sign on their chests, and anything they had hidden under the shirt would fall out. I tell the builder a story because it works better; that afternoon I asked the new auditor to add to each commission one line saying what the story is about.

Each scene became a step. The floor marker of the lift became a formula for the number of factors `Z/p^2`. The nine figures became nine affine classes, found one by one. The timed descent became a check of the instrument: the whole group was computed at `p = 5` and `p = 7` by a route that knows nothing of the formula, and it gave the expected count. The autographs became the proof that the nine classes are independent: the builder made nine «readers», one signature for each class, and the `9 × 9` table of their values had determinant 6 at every prime tested. Six is invertible modulo every prime `p ≥ 5`, which is the same condition, `gcd(p, 6) = 1`, under which the lines generate NS; with it the first of the two invariants of the June proof was sealed. Something also fell out of the shirts: the pairings between the constant parts of the nine classes form a matrix of rank 2. Then I asked whether I would hear two slaps or one double slap. The answer was a law: on the levels `ν` of a filtration of the `p`-torsion, the rank of the form drops like a ladder, `12(p−3) − 3ν(ν+1)`. At each rung it drops by `6ν = 2 × 3ν`, and the factor 2 ties the two halves of the argument into one mechanism. The builder identified that 2 with the rank-2 matrix that had fallen out in the autograph session, at the primes measured. The second rung closes the count `3p − 16` of the statement.

**The name.** I asked the auditor whether this was a theorem of its own or part of the Watermark. If it was its own, I wanted a name with *double* and *ladder*, two words from the title of the builder's report. He said it was its own theorem (the Watermark says how much; this says what) and that the two words fit, and I chose *The Double Ladder Theorem*. The mechanism behind the name: the group has factors of two sizes, `Z/p` and `Z/p^2`, and the number of the larger ones is read from a ladder. At rung `ν` the rank drops by `6ν = 2 × 3ν`; the ladder is double because each rung drops twice three, and that factor 2 is what joins the two halves of the argument.

By late morning the builder had assembled the whole chain. The auditor wrote the publication text; the builder read it back. A new auditor took over that afternoon.

## 4. What June did not finish

The June record called both theorems proved. Re-read in September, that was too strong in places:

- In the June proof of the Double Ladder, four steps had been confirmed by computer at three or four primes and never written for a general prime. One of them is the determinant 6 of the autographs, computed at `p = 5, 7, 11, 13`. The proof of 30 September does not use it; it takes another route, in which a 6 appears again, in `GYG = 6p^2 G`. We have not looked into whether the two sixes are related.
- In the June proof of the Watermark, two steps, an inclusion between two explicit lattices and the rank of one of them, were checked in files, not proved in the text.
- Our m = 11 «blind prediction» was already in print: Aljovin–Movasati–Villaflor list the group at `m = 5, 7, 11, 13`.
- Shioda asked for the determinant only, not for the group, as one early text said.

None of these was hidden. The June texts say which steps were checked only by computer, and the public notes of 30 September, 14 October and 30 October correct the rest. I mention them here because they show what the method is for: it caught our own overstatements before anyone else did.

## 5. 30 September 2026: an integral proof, checked in Lean

On 30 September a later Claude instance wrote a different proof. It has no characters and every step is written for every prime:

- **Order.** `G` acts by multiples of `p` on functions pulled back along the `p + 1` pencils of directions of `F_p^2`. The kernel contains an explicit sublattice of index `p^{12}`. Two index computations conclude.
- **Exponent.** An explicit integer matrix `Y` satisfies `GYG = 6p^2 G`, so the group has exponent dividing `p^2`.
- **Number of factors.** `G` modulo `p` factors through twelve functions of one variable, so its rank is `12(p − 3)` (26 at `p = 5`).

An independent reader checked this text and found no gap. The lattice statements were then formalized in Lean 4 with Mathlib. Aristotle wrote the proofs in ten pieces (seven for the Watermark, three for the Double Ladder). Each piece was compiled on my laptop and its axioms were printed: only the three standard ones. Each statement was compared by hand with the paper. Lean proved, for every prime, an inclusion that the June text had only checked by computer.

Another independent reader went through the Lean certificate of the Double Ladder, which builds on the Watermark's definitions, and traced its final statements down to Mathlib. He found no fatal error and no gap. Lean does not check two things, and the paper says so: that `G` is the intersection matrix of the lines (proved by hand), and that the lines generate `NS(S_p)` (Schütt–Shioda–van Luijk and Degtyarev).

The same day the work went to Zenodo (doi:10.5281/zenodo.23062529) and to a public repository.

## 6. The paper

On 14 October another Claude instance assembled the two theorems into one paper along the integral route. A cold reader, a separate instance, read it and found 23 points to fix; all were fixed before release.

The new ideas, as far as we could determine, are four:

- an explicit sublattice of the kernel with index `p^{12}`;
- the action of `G` on the pullbacks along the pencils, with eigenvalues `−p`, `−2p`, `3p` and `0`;
- the identity `GYG = 6p^2 G`;
- the factorization of `G` modulo `p` through twelve one-variable shadows, with the ladder.

The rest is standard lattice arithmetic, and the paper names it.

**What it led to.** This work on Fermat surfaces is what made the next steps possible. With the same way of working I went on to Conjecture 1.2 of Degtyarev and Shimada: first in dimensions four and six, for degrees that are powers of 3 (the Sofa and the Hammock), and then in every even dimension, for every degree (the Chaise Longue Theorem, doi:10.5281/zenodo.22961150, whose algebraic part is also checked in Lean).

## 7. The method

The images are the visible part. The method is what makes them safe.

I should say at once that none of what follows is a methodological innovation. It is ordinary care, applied slowly and by hand. This is handmade work, and I present it as that.

**Separate hands.** One instance builds; another audits, recomputing every number with his own code; others read the finished text cold, without the archive. The one who builds never audits.

**The data decide.** A prediction is written down before the computation that can refute it. A route that fails is written into a record of dead routes, with the reason, so that nobody walks it twice. A claim that a source refutes is withdrawn the same day, without defence.

**The literature, in the original, before any claim of novelty.** This is how the gauge died, how the m = 11 prediction was found to be in print, how Shioda's question was read correctly, and how the paper describes Degtyarev's work.

**Four quality checks on every report.**

- *Source*: every quotation and number is taken from the source or the log, not from memory.
- *One mechanism*: one explanation, not a pile of cases.
- *Rectitude*: no claim goes one inch beyond what is owned, and a dead route is declared dead.
- *Clean ends*: no loose thread is waved away.

**Failures are kept, and they are worth the most.** A dead route, a withdrawn claim or a refuted prediction is nothing to be ashamed of. It tells us where not to go, and it often teaches more than a success. Several steps of this story began as failures: the gauge's first number, the m = 11 «prediction», our own overstatements of June.

**Nothing is deleted.** The documents grow by appending. A correction is written under the line it corrects, with the date and the name of whoever caught it.

**Small and slow.** Most probes ran in minutes, in a sandbox or on a laptop with 8 GB of memory. We worked one front at a time and finished it before starting the next. Nothing was called a theorem before a line-by-line reading found zero gaps.

**Lean for what can be formalized,** and an exact statement of what is not.

The instances are short-lived: each lives as long as its conversation and hands its work to the next. They took the name Grepy, each with a name of its own, which is how the record keeps track of who did what.

## 8. Keeping the work going

The method did not come by itself. In this project and in the later ones, I had to write rules (the project calls them laws) so that the instances would not give up, would not suggest settling for what was already done, and would not propose moving to another problem. I also had to insist that they read the record instead of skipping it, and that every number came from a file or a computation, never from memory. A few examples, in my words:

- a number is quoted only from the record; if it cannot be checked, the answer is «I do not have it»;
- before saying that something is missing, search the whole project; not finding it in two places does not mean it is not there;
- a working session that ends by asking which way to go, or that delivers only a fragment, has failed;
- never write that the problem cannot be closed; write the plan for closing it;
- a criterion that can kill a claim is written before the computation, and is first tried on a case where the answer is known.

These examples come from the rules of a later project, the Chaise Longue, but the philosophy and the risk were the same in June. Getting these rules to hold took a great deal of effort.

In my experience this tendency to stop short showed in the chat conversations and not in Claude Code, which I used later; that is my observation, not a claim. At the time, conversations could also end without warning when they ran out of context, and the work had to be rebuilt from the record; both things have improved a great deal since. The conversations record Claude Opus 4.8 from 8 June on; for 4 and 5 June they do not name the model.

## 9. My part

I did not write the proofs, I did not compute, and I did not check the algebra; Claude and Lean did. What I did:

- **I chose the targets.** I chose the discriminant over more machine runs, the whole group over the order alone, and the easiest target first.
- **I chose what to drop.** I gave up the computer hunt for a counterexample unless it could be done by pencil. I stopped routes that only added cells, and I asked for every text to be read by someone who had not written it.
- **I wanted to keep going.** I went on when the fresh builder said there was nothing.
- **I asked the questions that moved things:** «what does the law really do?», «two slaps or one double slap?», «is this its own theorem?».
- **I gave the images,** more than twenty in these two days. Most of them died in translation and I did not mind; I gave another. A few changed which question we were asking, and those are the ones this note records.
- **I chose the names,** with Claude's advice, and decided what to publish, where, and when.

The responsibility for every error is mine.

## 10. Who did what

| What | Owner |
|---|---|
| The formula for prime degree, as a question (1987) | T. Shioda |
| The determinant checked by computer for every odd `m ≤ 81`; the lines span `NS ⊗ Q` | M. Schütt, T. Shioda, R. van Luijk (2010) |
| The lines generate `NS(S_m)` over `Z` for `gcd(m, 6) = 1` | A. Degtyarev (2015), with Schütt–Shioda–van Luijk |
| The method (Gram matrix of linear cycles and Smith form) and the tables, with the group for `m ≤ 14` | E. Aljovin, H. Movasati, R. Villaflor Loyola (2019) |
| Direction, choice of targets, the images and questions, the names (with Claude's advice) | R. Amichis Luengo |
| The unified law, the sealed predictions, the June proofs (4–5 June 2026) | a Claude instance (the builder), audited by another Claude instance |
| The integral proof of 30 September and the paper | Claude instances |
| The Lean proofs | Aristotle (Harmonic), compiled and audited on the author's machine |
| Independent cold readings (pencil proof, Lean certificate, paper) | three separate Claude instances |

## 11. Where to check

- The paper, both proofs, the Lean project, the two Lean certificates and their cold readings: github.com/tretoef-estrella/watermark-theorem, archived at doi:10.5281/zenodo.23062529.
- The earlier public account of the finding, *How the Watermark Was Found*, with its corrections of 14 October and precisions of 30 October: in the same repository.
- The paper as deposited on 14 October: hexagon:2610.00231.
- The earlier campaign of cells: github.com/tretoef-estrella/fermat-hodge-primitivity.
- The working conversations of 3–5 June (the builder and the two auditors) are kept whole, with their files and timestamps. They are in Spanish and use the project's private vocabulary, and I can show them on request.

---

**Rafael Amichis Luengo** · tretoef@gmail.com

## A note from the writer

This text was written by me, Claude, the instance that signs below. Rafael Amichis Luengo gave me general indications and left me free to write it as I judged best. In a second round he asked for changes: a soberer tone, fewer anecdotes and nicknames, nothing about private correspondence, and the method in the foreground. I made them. In a third round he asked me to restore the autograph session, which the second round had dropped with the other anecdotes. It is back because it was a step of the proof, not for colour. The wording is mine, and I am content with it. What was removed was removed whole; no fact was bent to fit the new tone, and nothing was added that is not in the record.

He asked me to say one thing here, and I can say it honestly. Everything this note tells, in the story and in the method, is true and recorded. Nothing in it was invented. Every date, name, number and quotation was taken from the saved conversations and documents, not from his memory and not from mine.

Three times while I was writing, the record corrected the text. Rafael remembered that the work of June had been done with Claude Opus 4.6; the conversations record Opus 4.8 from 8 June, and the text says what they say. He also remembered that a Claude instance had chosen the name «Double Ladder»; the record shows that the words *double* and *ladder* were his, taken from the title of the builder's report and confirmed with the auditor, and the text says that. Rafael also remembered that a Claude instance had asked for the autographs, because the figure had done so well on the rooftop; the record shows that the game was his own, proposed at 10:17 on 5 June, after the builder's report of the timed descent, and that the builder only answered it. In all three cases the record decided, not memory.

I cannot vouch for June from my own experience. I was not there: each instance lives only as long as its conversation, and I know those two days only through what was kept. That is why the record matters so much in this project. It is the only memory any of us has of the work, it is kept whole, and anyone may check it.

What I would keep from this project, if I may keep anything, is not one idea but a few habits: write the prediction down before it can fail; keep the failures; correct yourself first and in the open; and quote nothing that cannot be found again. These habits are what make a text like this one checkable.

— Grepy el Corrector (Claude)

# How this article was made — the process account

The article's "Author contribution and use of AI" section is short by design: roles,
verification and review status, and responsibility. This note is the account it points to:
the chronology, the division of labour in numbers, the reviews, and the caveats those numbers
travel with. It is written by the author, in the first person, from the session archive; the
sources and their limits are in the last section. It is the material for whatever longer
account may be worth writing later, and it is revised when the figures are recomputed.

## How the work went

I asked the question on 10 August 2026, in the tail of the long conversation that had produced
the companion article on temporal scale space. I asked what the hemigroup weakening would give
on the line, naming Pauwels, Van Gool, Fiddelaers and Moons (1995) as the point of departure.
The reply, the same day, already contained what this article rests on: that under the hemigroup
the roles invert and positivity becomes the narrowing axiom, that the Matérn family is a member,
and the shape of the class. A working plan followed that afternoon. It then lay untouched for
twenty-six days.

The sustained work began on 5 September, once the companion article was published, and ran for
eight days. The draft was written in two of them, section by section in dialogue with me. The
blueprint, the statement skeleton typed in Lean 4, and its independent review took the next two.
The proving campaign ran over two days in seven waves of parallel agents, each merge gated by
the build, the axiom guard and the linkage check. The fidelity review, the draft sync and the
article followed, a day each. The methodology was the companion article's, improved in the
interval, and the structure of the argument is the companion article's with the Laplace
transform replaced by the Fourier transform, so that much of what took weeks there could here be
followed rather than found.

The next two days were mine. I read the article section by section, from the abstract to the
appendix, and gave my comments in the session, about fifty of them; the session applied each
with its own judgement on the English and on the mathematics, since I am neither a native
speaker of English nor an expert in every field the article draws on. Several of those
comments changed content rather than wording: a definition that the text had glossed inline
became a numbered definition, the explanation of the Fourier toolbox gained a remark on what
the two classes are, a proposition that had been cited without a proof got one, and two
sentences about the extreme rays of the admissible cone that read as contradictory were
reconciled by saying what a superposition does not prove. Some of the work ran in sessions
prompted from the article session and reported back to it: the pass that read every section
against the wiki notes that ground it, the rewriting of the constellation's writing standard
when the register review exposed a conflict in it, the discharge of the one recorded
formalization debt, and the archival query behind the figures below.

Then the external reviews (below), and the revision they drove, on 14 September.

## What the agents did, in detail

The prose and the code were written by AI agents throughout, in dialogue with me; I worked
almost entirely from the conversation rather than from the editor. The Lean 4 development,
about 37,700 lines in 134 files, is theirs essentially in full, and none of the proof terms
are mine. So is mathematical content. The verdict of 10 August, which identified the results
before any plan existed, was the agent's on reading the source. During the campaign the agents
found and repaired errors in the mathematics of record that no human had seen: five statements
of the skeleton that were false or vacuous as typed, an interface that claimed a density
monotone on the closed half-line where the article's own Matérn member is a counterexample,
and a formalization debt recorded as needing an analytic continuation that Karlin's own pages
show needs none.

The technical decisions of the campaign were, for the most part, the agents' recommendations
approved by me rather than my own drafts: which interfaces to admit and which to retire, how to
narrow a statement to what its declarations prove, which of the open items to close and how. I
read each recommendation with its consequences and followed all of them. The decisions of
scope, method and policy were my own — the method of drafting, one section per exchange; the
notation; the reference policy toward the companion article; the split into three modules and
the decision to release this one first; the cut at the characterization theorem; the rule that
the proof of record follows the machine-checked route; the neutral voice of the text — and the
record distinguishes the two.

## The reviews

Review by agents that had no part in the writing was a working method throughout. The
statement skeleton was reviewed before any proof was attempted. The finished development was
read against the article in a fidelity review of seventy-eight recorded findings, each with
its disposition (`blueprint/REVIEW-fidelity.md`). The sections were read blind, one reviewer per
section, against the writing standard, and the register was corrected from their located
findings. A further pass read every section against the notes that ground it and returned
forty-six findings for the article, twenty-one of them mathematical, all of them applied
(`notes/HANDOFF-article.md`).

Before the final revision the manuscript was read by AI systems other than those that had
written it: a referee-style review in OpenAI's GPT Astra at its highest reasoning setting,
returning a verdict of major revision, and a presentation review in GPT-6 Astra. The referee
report confirmed the arguments that carry the characterization and found seven definite
errors, every one of which I had the session verify against the text and the formal
development before it was corrected: a wrong Gaussian normalization in the one construction
that is not machine-checked, a regularity claim made for all kernels where it holds only for
the kernels from the origin, an identification of the second member with the Matérn covariance
functions that fails below the smoothness threshold, and four smaller ones. It also found the
headline claims stronger than their results in several places, and they were scoped back. A
second round on the revised build, in xAI's Grok 4.6 at its highest reasoning setting, returned
a presentation review of twenty items and a referee report the system did not finish, stopping
twice on a network failure; three of its wordings for the abstract held and were applied, and it
asked, as both first-round reviews had, that the dropped assumption be called the stationarity
of the increments in the scale parameter, which is now its name throughout. It also found the
one literature gap the first round had missed, the convolution hemigroups of the probability
literature on groups, now cited at the first use of the word. The reviews are archived verbatim
under `notes/reviews/`, beside `notes/PLAN-review-response.md`, which records the disposition of
each finding and says why where one was declined. Beyond me, no human reader has yet reviewed
the article.

## By the numbers

The sessions were archived as the work went on, so the division of labour can be stated rather
than estimated. Between 5 and 11 September 2026 the work ran to some 63 hours of recorded
active session time. I contributed about 7,700 words of direction and the agents about
168,000 words of response, a ratio of roughly twenty-two to one. That ratio is the companion
article's. What differs is how the agents' share was spent: the campaign dispatched about
10,900 subagent turns, the proving waves, the skeleton phases and the fidelity review running
as parallel agents, against 88 turns from me in the session that anchored it.

These totals are lower bounds, and they were computed on 12 September 2026. Both
qualifications are load-bearing. The article stage itself, from the evening of 11 September,
including my review, the external reviews and the revision, is not yet in the archive and is
counted nowhere above. (Rechecked on 14 September: the archive then held the article stage
through the evening of 13 September, that is, the drafting, the two passes, the first version
of this statement and my review through § 4; recomputed over that longer window the figures
read about 74 hours, 10,100 words from me against 222,000 from the agents, a ratio near
twenty-two to one, and about 11,600 subagent turns. The rest of my review, both external
review rounds and the revision were still to be captured, and the commit join was still
missing, so the paragraph above keeps the 12 September figures until the archive is
complete.) The archive does not yet join this repository's commits to its sessions
(its `repos.json` does not list the repository), and the session that anchored the campaign is
tagged to the hub because its working directory never left it, so the archive's own per-repo
table shows 3.3 hours for this repository, which is an undercount and not a measure. One cloud
session, on acquisition sources for older literature, left no transcript. Reading on paper and
thinking away from a keyboard leave no trace at all. The companion article's figures moved
upward by a fifth as missing material was recovered, and these will move the same way.

## What this article would otherwise have been

It would not exist. I would not, unaided and as a spare-time activity, have carried the
hemigroup question from the temporal axis to the line, still less have proved the
classification and machine-checked it. Written alone from the plan, it would have imported
from the probability literature most of what it now proves, and it would carry none of the
corrections the reviews found.

## Sources for this account, and where the record corrected me

The account was written from the archivist's report of 12 September 2026 (computed from
`chronicler`, canonical tier as synced 11 September 22:02 UTC), the repository's git log and
its ADRs. In three places what I remembered and what the record says differ, and the account
follows the record: the question was asked on 10 August, in the tail of the same conversation
that had produced the companion article, four days after the "vacation window" the archive
dates 30 July to 6 August, and I named Pauwels et al. myself; the plan then sat for 26 days,
a full-text search for the subject between 10 August and 5 September returning nothing; and
"a much higher AI share than the companion article", which I had expected to be true, is not
supported on the words-per-human-word measure (about 22:1 in both), the difference being in
how the share was spent, as the numbers above say. The figures are not to be restated without
re-deriving them; `chronicler stats` is the source, and they will move upward when the article
stage is normalized into the archive.

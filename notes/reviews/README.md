# External reviews

Referee-style reviews of the article solicited by the author from AI systems other than those
that wrote it, against a frozen PDF build, and archived here verbatim as provenance. The
procedure is Paper I's (`hemigroup-causal-scale-space-kernels/notes/reviews/`): the author runs
the prompt in `PROMPT-external-review.md` in each system's own interface with the PDF attached,
saves the output here unedited under a filename carrying the attribution (the system, and its
reasoning-effort setting where one was chosen), and the article session then assesses every
finding independently and records the disposition in `../PLAN-review-response.md`.

**The reviewed build** is the article at repo revision `09602a3` (2026-09-14, 48 pages, the
end of the author's own review), built with `tectonic paper/main.tex`. Page references inside
the reviews are to that build; section and statement numbers may shift in the revisions the
reviews drive.

The reviews are inputs to the revision process, not statements by the author; where a
review's claim is found wrong or out of scope, the response plan says so. No finding is acted
on because a reviewer asked for it alone.

## Files

- `PROMPT-external-review.md` — the prompt, in two parts: the journal-style review and the
  shorter presentation review.
- `line-review-content-GPT-Astra-Ultra.md` — part A, run by the author on 2026-09-14 in
  OpenAI's GPT Astra at the Ultra setting; verdict *major revision*. This is *the review* that
  `../PLAN-review-response.md` responds to, finding by finding.
- `line-review-presentation-GPT-6-Astra-Extra-High.md` — part B, run the same day in GPT-6
  Astra at the Extra High setting; twenty ranked presentation items, worked into the response
  plan's batches R2, R3 and R6.

Both files are verbatim as saved from the interface, including its citation artifacts
(`:codex-file-citation{…}`), which refer to the reviewed PDF on the author's machine.

**Second round.** After the response to the first two reviews (batches R1–R6 and the seven
decisions of `../PLAN-review-response.md`, 2026-09-14), a second build was frozen at revision
`768625d` (49 pages) for a further referee-style review in xAI's Grok, part A of the prompt
only. Its purpose is to test whether the corrections hold up and what a second reader finds
that the first did not; page references in that review are to the second build.

- `line-review-presentation-768625d-Grok46-ExtraHigh.md` — part B on the second build, run
  by the author on 2026-09-14 in Grok 4.6 at the Extra High setting (200K context); twenty
  ranked items, worked into the second section of the response plan.
- `line-review-content-768625d-Grok46-partial.md` — part A on the second build, run by the
  author on 2026-09-14 in Grok 4.6 through a Copilot environment that did not finish; the
  output up to the stop is archived verbatim (with the interface's stray combining
  characters), and its page references are not the build's. The run stopped twice on
  network errors and is not expected to complete, so the partial output is the record;
  assessed as it stands in the response plan's second-round section.

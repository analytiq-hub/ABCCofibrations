# Planning and development process

We are formalizing Anderson–Brown–Cisinski cofibration categories incrementally,
following Andrei Rădulescu-Banu's
[*Cofibrations in Homotopy Theory*, arXiv:math/0610009v4](https://arxiv.org/abs/math/0610009v4).
The aim is a reusable Lean library whose statements can be traced back to the
mathematics, with each increment small enough to understand and review.

The [formalization plan](formalization-plan.md) records milestones, implemented
declarations, outstanding work, and build evidence. This document explains how
we choose and carry out that work; it is not a second progress tracker.

Related community discussion:
[“Newbie question about how to best formalize an article,” Lean Zulip,
`new members`](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Newbie.20question.20about.20how.20to.20best.20formalize.20an.20article/with/638441863).
The link is provided for context; the process below describes this project's
practice and does not attribute particular recommendations to that discussion.

## 1. Plan around mathematical dependencies

Begin with a broad roadmap, then expand only the early stages into concrete work
packages. Each package should identify a definition, a theorem, or a small group
of closely related results, together with its prerequisites and completion
criteria. Later milestones remain provisional until their dependencies are
understood.

The order need not match the printed order of the paper. A useful next result
is one whose prerequisites are available and whose interface supports subsequent
proofs. For example, finite coproducts support Brown factorization and cylinder
existence; relative factorization supports relative cylinders. When work moves
ahead of an unfinished section, leave that section explicitly outstanding in the
plan.

Before implementing a result, record:

- Its reference in the fixed version of the paper.
- The intended statement, including all cofibrancy and size assumptions.
- The results needed for its proof.
- What will count as complete, including any comparison maps or equations that
  later arguments need.

## 2. Inspect mathlib before choosing an interface

Search both the project and the pinned mathlib source for existing definitions,
lemmas, and constructions. Read their actual assumptions, rather than relying
on their names. Keep the project's Lean and mathlib versions fixed during
ordinary proof development so that interface changes are deliberate.

Reuse established abstractions where their meaning fits. For example, we use
mathlib's morphism classes and cofibrant objects, and represent the paper's
cylinders by mathlib's `Cylinder` equipped with `Cylinder.IsGood`.

Reusing a definition does not mean its existing theorems apply under our
assumptions. Several mathlib cylinder and coproduct results assume a model
category or unrestricted pushout stability. ABC proofs must retain the
cofibrancy restrictions of CF3 and distinguish CF1–CF4 from CF5–CF6.

Prefer explicit existence theorems and local instances when a construction is
available only for cofibrant objects. Accept callers' chosen coproducts and
pushouts where practical. Avoid introducing global instances that assert
stronger closure or existence properties than the axioms provide.

## 3. Translate the statement before developing the proof

Write the Lean statement with its mathematical interpretation in view. Check
arrow directions, composition order, the distinction between existence and
chosen data, and the universes of objects, morphisms, and indexing types.

Expose useful witnesses and their equations. A relative factorization, for
example, should retain the comparison map from the pushout and the equations
that identify it as the canonical comparison. An existential result is often
enough initially; introduce a structure or a chosen construction when downstream
use gives a concrete reason to do so.

In explanatory documents, use the paper's notation, rendered equations, and
diagrams. When Lean names differ, provide a short correspondence table. This
lets mathematical review proceed without requiring the reader to decode Lean
syntax first.

## 4. Develop and verify one increment at a time

Implement the smallest useful result first, compile it, and resolve failures
before building the next layer. Extract categorical helper lemmas when they
capture a reusable universal-property or pasting argument. Keep proof modules
organized by coherent mathematical subjects.

Use targeted compilation during proof development, then run the full library
build:

```sh
lake env lean ABCCofibrations/SomeModule.lean
lake build
```

Resolve warnings as well as errors. Export a completed module through the library
root when it belongs to the public library. Do not import unfinished statements
with `sorry`, `admit`, or new axioms to make later work appear complete.

A successful build establishes that Lean accepts the formal statements and
proofs under their declared assumptions. It does not by itself establish that
those statements faithfully express the paper. Source correspondence and
mathematical review remain separate checks. For substantial results, inspecting
`#print axioms` can also confirm that no unintended assumptions entered the
proof; Lean's ordinary foundational axioms are distinct from added mathematical
axioms or `sorryAx`.

## 5. Treat discrepancies as mathematical work

When a source statement appears problematic, first check the transcription,
notation, hypotheses, and available interfaces. Then test a small example and
try to isolate the obstruction. A failed proof attempt alone is not evidence
that a theorem is false.

If a counterexample survives that examination:

1. Write a precise account of the original claim and the obstruction.
2. State a corrected result with explicit hypotheses and conclusions.
3. Prove the corrected result and record what has actually been formalized.
4. Audit downstream arguments for the properties they need.
5. Search for earlier corrections and references, distinguishing a failed search
   from evidence of novelty.

The [relative Brown factorization note](relative-brown-factorization.md)
illustrates this process. It separates the corrected statement, proof,
counterexample, historical information, references for the ambient category,
and the scope of Lean verification. The gluing proof was then repaired using
restricted comparison properties proved under the cofibration hypotheses that
the argument actually has.

## 6. Keep the record aligned with the code

After an increment passes the full build, update the plan with the declaration
names, source references, relevant interface decisions, and validation result.
State what remains open. Distinguish completed results from planned work,
informal arguments from checked proofs, and corrected statements from the
original claims.

Human review determines the mathematical scope and checks whether the
formalization captures it. An assistant can search interfaces, propose
statements, construct proofs, and maintain documentation, but its explanations
still require review. Lean checks the proof terms; it does not certify historical
claims, bibliographic priority, or the adequacy of a proposed correction.

Before a requested commit, review the diff, run `git diff --check`, and ensure
the relevant build has passed. Keep commits focused on coherent increments.
Commit and push when requested, and report their actual outcome separately
from implementation or validation status.

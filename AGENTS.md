# AGENTS.md

## Project overview

This repository formalizes parts of determinantal ideal theory in Lean 4, with the long-term goal of proving that the set of `t × t` minors of the generic matrix is a Gröbner basis under a diagonal term order.

The codebase is not a generic Lean playground. It is a research-style formalization project built around:
- determinantal ideals
- minors of generic matrices
- diagonal term orders
- Gröbner basis machinery
- compatibility with existing Lean / Mathlib / external Gröbner APIs already used in this repository

When working in this repo, prefer small, local, proof-oriented changes over broad refactors.

---

## Main working principles

1. **Preserve mathematical intent.**
   Do not rewrite a theorem into a materially different statement unless that is explicitly requested or clearly necessary for compilation.

2. **Prefer API alignment over cleverness.**
   Reuse existing definitions, lemmas, namespaces, and theorem shapes already present in this repository.
   In particular, prefer adapting to the existing determinantal-ideal and Gröbner-basis APIs instead of inventing parallel abstractions.

3. **Do not perform large refactors by default.**
   Avoid renaming many lemmas, changing file structure, or rewriting large proof blocks unless the task explicitly asks for it.

4. **Prefer proof skeletons with useful intermediate lemmas.**
   If a target theorem is hard, introduce small helper lemmas with clear names and mathematically natural statements.

5. **Verification should be targeted, not automatic.**
   Do not run `lake build MyProject` after every meaningful edit by default.
   Prefer small exploratory proof attempts first.
   Only run a build/check command when:
   - the user explicitly requests verification, or
   - a command is genuinely needed to diagnose an error or confirm a near-finished result.

6. **Be honest about blockers.**
   If a proof attempt fails, explain the exact obstruction:
   - missing lemma
   - wrong theorem statement
   - typeclass issue
   - coercion / elaboration mismatch
   - existing API incompatibility
   - mathematically incorrect subgoal

---

## Repository focus

Important themes likely to appear in tasks:
- `genericMatrix`
- `MinorIndex`
- minors and minor sets
- determinantal ideals
- evaluation / base-change lemmas
- diagonal term orders
- leading term / degree / leading coefficient lemmas
- Gröbner basis statements for minors
- paper-guided formalization of proofs from the generic minors literature

When solving tasks, keep these themes in mind and search for existing supporting lemmas before introducing new definitions.

---

## Files and navigation

Start by inspecting the files most relevant to the task. Common important files may include:
- import aggregator files such as `MyProject.lean`
- files defining generic matrices, minors, and determinantal ideals
- files about diagonal orders / minor leading terms
- files related to Gröbner machinery
- files such as `PaperWay.lean` that mirror a paper proof structure

Before editing, locate:
- the target theorem
- nearby helper lemmas
- notational conventions already used in the same file
- imported modules that already provide the needed infrastructure

Prefer following the local style of the file you are editing.

---

## Build and check commands

Use the smallest command that gives reliable feedback, but do not run any command by default unless it is requested or necessary.

Typical commands:
- `lake build`
- `lake env lean <path-to-file>`
- `lake build MyProject`

Preferred policy:
1. For small exploratory Lean proof tasks, do not run a build/check command unless explicitly requested.
2. If verification is requested, prefer the smallest focused command first.
3. Only use a broader build when the user asks for it or when broader confirmation is genuinely needed.
4. If no check command is run, explicitly say that the code is unverified.

Do not claim compilation succeeded unless a command was actually run.

---

## Lean proof style for this repository

1. **Prefer existing lemmas first.**
   Search before proving something from scratch.

2. **Use small `have` blocks for difficult proofs.**
   Break long proofs into named steps.

3. **Avoid overusing brittle `simp` if it obscures the argument.**
   Prefer controlled rewriting when the proof is mathematically structured.

4. **Be careful with implicit arguments and coercions.**
   This repository uses objects such as:
   - `MvPolynomial`
   - `Ideal`
   - `MonomialOrder`
   - matrix minors
   - embeddings / order embeddings
   - degree / leading term APIs

   Elaborator issues are common. When necessary, make arguments explicit.

5. **Do not replace a precise theorem with a weaker version just to make it compile.**
   Any weakening must be clearly justified.

6. **Prefer mathematically meaningful helper lemmas.**
   Good helper lemmas usually:
   - match the paper proof
   - isolate a coercion-heavy step
   - expose a reusable structural fact
   - improve later theorem statements

---

## Preferred workflow for hard theorems

For hard theorem-proving tasks, use this order:

1. Read the target theorem and surrounding context.
2. Identify which part is:
   - algebraic / mathematical
   - API / typing / coercion related
3. Search for nearby lemmas that already express most of the needed statement.
4. If the proof is nontrivial, first write a proof skeleton with `have` steps or helper lemma declarations.
5. Try to prove the helper lemmas in dependency order.
6. Only run a build/check command when explicitly requested or when needed to diagnose an issue.
7. If blocked, leave a precise explanation instead of making random changes.

When a theorem is obviously too large to finish in one shot, prefer turning one opaque failure into 2–5 clear intermediate lemmas.

---

## What to avoid

Do not:
- introduce new parallel abstractions when existing ones suffice
- rewrite many finished proofs for style only
- delete comments or documentation unless outdated or wrong
- change theorem names casually
- use `axiom`, `admit`, or unsafe placeholders
- silence failures by weakening statements without explanation
- make broad import changes unless necessary
- switch the mathematical strategy without saying so

Do not assume a missing lemma does not exist until you have searched nearby files and imports.

---

## Mathematical strategy guidance

This project often follows paper-style proofs. When possible:
- preserve the natural mathematical decomposition from the source proof
- separate combinatorial lemmas, determinant lemmas, and Gröbner-order lemmas
- keep “paper translation” lemmas close to the paper structure
- keep “API bridge” lemmas separate when they mainly help Lean connect existing results

If there are two possible proof routes:
- prefer the one better aligned with the current repository structure
- prefer the route that reuses already formalized sections
- prefer smaller reusable lemmas over a giant one-shot proof

---

## Done criteria

A task is done only when all of the following hold:

1. The proof matches the requested theorem statement.
2. The change is local and does not introduce unnecessary breakage.
3. New helper lemmas have sensible names and are placed in a reasonable location.
4. If a build/check command was requested or run, the final response accurately reports the result.
5. The final response explains:
   - what changed
   - whether any command was run
   - whether the result is verified or unverified
   - any remaining blocker or limitation

If full completion is impossible, report the furthest valid partial progress and the exact blocker.

Do not describe code as compiled or verified unless a corresponding command was actually run.

---

## Response expectations

When reporting back after edits, include:
- which files were changed
- which theorem / lemma was proved or partially refactored
- which command was run, if any
- whether verification succeeded, if any command was run
- if no command was run, clearly say the code is unverified
- if blocked, the exact reason

Keep the response concrete. Prefer compiler-grounded explanations over vague statements.

---

## Repository-specific preference

This is a theorem-proving codebase, not an application codebase.
Correctness, theorem shape, and compatibility with existing proof infrastructure matter more than brevity.

For this repository, a good change is usually:
- mathematically faithful
- easy to build on later
- aligned with existing theorem names and structures

A bad change is usually:
- “clever” but hard to reuse
- dependent on fragile elaboration accidents
- mathematically off-route
- a large refactor done without necessity

---

## Current project focus

The current high-priority direction is to support the eventual proof of the Gröbner basis theorem for minors under a diagonal term order.

When tasks concern `PaperWay.lean` or nearby files:

1. Prefer following the proof structure of the source paper.
2. Distinguish clearly between:
   - paper-translation lemmas
   - helper lemmas introduced only for Lean engineering
3. If a theorem is difficult, first produce a skeleton that reveals the missing intermediate lemmas.
4. Prefer helper lemmas that can later be reused in the final Gröbner basis proof.

When editing proofs around proposition-style paper formalization:
- keep theorem names descriptive
- preserve index conventions already used in the file
- avoid re-encoding the same combinatorial object in a different way unless necessary

---

## Special instructions for theorem proving

If the target theorem does not compile immediately:

1. Do not keep retrying random tactics.
2. Inspect the goal state and identify whether the problem is:
   - missing rewrite
   - wrong coercion
   - missing side condition
   - missing helper lemma
   - wrong formulation
3. If the issue is structural, stop and propose the missing intermediate lemma explicitly.
4. Prefer one solid intermediate lemma over many tiny throwaway lemmas.

When a proof depends on a fact that is likely already in Mathlib or in this repository, search for it first.

---

## Editing discipline

Before changing a theorem statement:
- check how it is used elsewhere
- prefer adding a wrapper lemma instead of changing downstream APIs
- if a statement must change, explain why in the final report

Before adding imports:
- verify whether the needed result is already available through existing imports
- keep imports minimal unless a broader import is clearly justified
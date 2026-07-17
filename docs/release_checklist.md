# AFM Submission and Artifact Release Checklist

This checklist distinguishes automated repository checks from manuscript and
submission checks that require review by the author. Passing the artifact audit
alone does not certify the manuscript as ready for submission.

## Repository readiness

1. Verify that the repository is publicly accessible, carries an open-source
   license, and contains every source file needed to check the formal results.
2. Verify that the working tree is clean.
3. Run `lake exe cache get`.
4. Run `bash scripts/check_artifact.sh`.
5. Commit the final source, documentation, and tooling changes.
6. Verify that CI passes on that exact commit.
7. Verify the exact committed revision from a fresh clone: check out the
   intended immutable commit or tag, run `lake exe cache get`, and run
   `bash scripts/check_artifact.sh`.

## Manuscript-to-artifact correspondence

8. Verify that the manuscript maps each main informal result to a formal
   declaration and explains every representation choice, each stronger or
   weaker aspect, all totalized edge cases, and the unformalized geometry. Use
   [`statement_correspondence.md`](statement_correspondence.md) as the audit
   source.
9. On a clean working tree, run
   `python3 scripts/artifact_metadata.py --require-clean --format markdown`
   and record the exact Lean toolchain and version, the requested revisions and
   resolved commits for Mathlib and `groebner_proj` (the `groebner` Lake
   dependency), and the artifact commit in the manuscript or artifact
   appendix.
10. On the same clean working tree, run
    `python3 scripts/paper_links.py --format markdown` and assign every main
    result a fixed link to the cited revision. Do not use the mutable `main`
    branch as final manuscript evidence.
11. Verify that code excerpts in the manuscript are limited to places where
    they materially complement the mathematical exposition.

## Submission and archival steps

12. Deposit the manuscript PDF in an open archive accepted by AFM (HAL, arXiv,
    or Zenodo) before submitting it through Episciences; do not place the PDF
    inside a zip archive for submission.
13. Create an annotated artifact tag, for example
    `afm-artifact-v1.0.0`; the author chooses the final tag name.
14. Create a GitHub release from exactly that annotated tag and archive the
    code release with Zenodo, Software Heritage, or another long-term service.
    Verify that the GitHub release and every archival record resolve to the
    same tag and commit. Standard source archives omit `.git`, so run the full
    audit from the fresh clone in Step 7 rather than from an unpacked archive.
15. Record any assigned DOI or archive identifier, together with the immutable
    artifact revision, in the manuscript and repository metadata. Do not add
    guessed identifiers.
16. Verify that the manuscript declares all funding sources and any potential
    conflicts of interest, cites every publication used, and is not
    simultaneously submitted to another journal.

## After acceptance

17. Upload the accepted AFM-formatted manuscript as a new version of the
    original open-archive record.
18. If available, provide AFM with a permanent Software Heritage identifier
    (SWHID) for the code repository and record it in the manuscript and
    repository metadata.

The AFM-specific portions of this checklist refer to the official
[AFM instructions for authors](https://afm.episciences.org/page/instructions-for-authors),
[aims and scope](https://afm.episciences.org/page/aims-and-scope), and
[publishing policies](https://afm.episciences.org/page/publishing-policies).

The workflow
[`create-release.yml`](../.github/workflows/create-release.yml) is a Lean
toolchain release helper triggered when `lean-toolchain` changes on `main` or
`master`. It is not the AFM manuscript-artifact freezing procedure.

After publication, the author may add verified article metadata to
[`CITATION.cff`](../CITATION.cff); do not add guessed DOI, venue, or issue data.

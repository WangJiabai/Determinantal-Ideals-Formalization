# AFM Submission and Artifact Release Checklist

This checklist separates repository checks that can be automated from
manuscript and submission checks that require an author. Passing the artifact
audit does not by itself certify the manuscript for submission.

## Repository readiness

1. Confirm that the repository is publicly accessible, carries an open-source
   license, and contains every source file needed to check the formal results.
2. Ensure the working tree is clean.
3. Run `lake exe cache get`.
4. Run `bash scripts/check_artifact.sh`.
5. Commit the final source, documentation, and tooling changes.
6. Wait for green CI on that exact commit.
7. Verify the committed revision from a fresh checkout or release tarball.

## Manuscript-to-artifact correspondence

8. Check that the manuscript explains how each main informal result maps to a
   formal declaration, including all representation choices, stronger or
   weaker assumptions, totalized edge cases, and unformalized geometry. Use
   [`statement_correspondence.md`](statement_correspondence.md) as the audit
   source.
9. Run
   `python3 scripts/artifact_metadata.py --require-clean --format markdown`
   and copy the exact Lean, Mathlib, `groebner`, and commit metadata into the
   manuscript or artifact appendix.
10. Run `python3 scripts/paper_links.py --format markdown` and give every main
    result a fixed link to the cited revision. Do not use links to the changing
    `main` branch as final manuscript evidence.
11. Confirm that code excerpts in the manuscript are limited to places where
    they materially complement the mathematical exposition.

## Submission and archival steps

12. Deposit the manuscript PDF in an AFM-supported open archive (HAL, arXiv,
    or Zenodo) before submitting it through Episciences; do not place the PDF
    inside a zip archive for submission.
13. Create an annotated artifact tag, for example `afm-artifact-v1`; the final
    name is chosen by the authors.
14. Create a GitHub release from that exact tag and archive the code release
    with Zenodo, Software Heritage, or another long-term service.
15. Add the verified DOI, archive identifier, and immutable revision to the
    manuscript and repository metadata. Do not add guessed identifiers.
16. Confirm that the manuscript declares all funding sources and any potential
    conflicts of interest, cites every publication used, and is not
    simultaneously submitted to another journal.

## After acceptance

17. Upload the accepted AFM-formatted version as a new version of the original
    open-archive record.
18. Provide AFM with a permanent Software Heritage identifier (SWHID) for the
    code repository when available, and record it in the manuscript and
    repository metadata.

The journal requirements referenced by this checklist are the official
[AFM instructions for authors](https://afm.episciences.org/page/instructions-for-authors),
[aims and scope](https://afm.episciences.org/page/aims-and-scope), and
[publishing policies](https://afm.episciences.org/page/publishing-policies).

The workflow
[`create-release.yml`](../.github/workflows/create-release.yml) is a Lean
toolchain/version release helper triggered by changes to `lean-toolchain`. It
is not the AFM manuscript-artifact freezing procedure.

After publication, authors may add verified article metadata to
[`CITATION.cff`](../CITATION.cff); do not add guessed DOI, venue, or issue data.

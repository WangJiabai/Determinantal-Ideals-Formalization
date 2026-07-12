# AFM Artifact Release Checklist

1. Ensure the working tree is clean.
2. Run `lake exe cache get`.
3. Run `bash scripts/check_artifact.sh`.
4. Commit the final documentation and tooling changes.
5. Wait for green CI on that exact commit.
6. Run `python3 scripts/artifact_metadata.py --require-clean --format markdown`.
7. Run `python3 scripts/paper_links.py --format markdown`.
8. Update the manuscript with the local HEAD, fixed source links, Lean/Mathlib/
   `groebner` versions, CI reference, and archive identifier.
9. Create an annotated artifact tag, for example `afm-artifact-v1`; the final
   name is chosen by the authors.
10. Create a GitHub release from that exact tag.
11. Archive the release through Zenodo, Software Heritage, or an equivalent
    long-term service.
12. Add the DOI or archive identifier to the paper and repository metadata.
13. Verify the tag tarball from a fresh directory.
14. Never cite the changing `main` branch as the final artifact.

The workflow
[`create-release.yml`](../.github/workflows/create-release.yml) is a Lean
toolchain/version release helper triggered by changes to `lean-toolchain`. It
is not the AFM manuscript-artifact freezing procedure.

After publication, authors may add verified article metadata to
[`CITATION.cff`](../CITATION.cff); do not add guessed DOI, venue, or issue data.

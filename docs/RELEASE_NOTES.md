# RHO5 v1.0.2 — expanded proof and dated exact replay

**Qianli Ma · Chao Wu.** Both authors are affiliated with Zhejiang University; the article additionally lists WUJIE AI for Qianli Ma.

This release is based on the fixed [v1.0.1 tag](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.1). The [cumulative changelog](../CHANGELOG.md) gives the differences from that release. The revised **88-page article and 9-page supplementary index** are archived as the preprint [DOI 10.5281/zenodo.23057256](https://doi.org/10.5281/zenodo.23057256). The previous [DOI 10.5281/zenodo.22727368](https://doi.org/10.5281/zenodo.22727368) identifies the v1.0.1 PDFs.

## Fixed v1.0.2 files

- [Article PDF · 88 pages](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/rho5_manuscript_v1.0.2.pdf) and [supplementary index PDF · 9 pages](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_SUPPLEMENTARY_INDEX_v1.0.2.pdf), matching the published Zenodo files
- [Article source and bounded checks](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_v1.0.2_source_and_checks.zip)
- [30 September replay evidence](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_v1.0.2_replay_evidence.zip)
- [Second-phase Lean source review](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.2/RHO5_Lean_Phase2_B366_SOURCE_ONLY_v1.0.2.zip)

The five attachments and their SHA-256 values are in [the v1.0.2 release index](../manifests/v1.0.2.json). For reading and verification:

- [Proof map](PROOF_MAP.md), [verification guide](VERIFY.md), [中文验证教程](VERIFY.zh-CN.md) and [download inventory](DOWNLOADS.md)
- [30 September negative-diagonal replay](REPLAY_20260930.md) and [full dependency protocol](REPRODUCIBILITY_PROTOCOL_v1.0.2.md)

Appendix B now exposes more of the analytic proof, including the representative and reconstruction steps and the complete-X entrance. The revised index points to frozen mathematical sources and exact acceptance entries. The theorem is a paper-and-certificate result. Its code dependencies and limits remain explicit.

## Recorded finite-cover replay

On 30 September 2026, an isolated run on the existing X Linux host checked all **570** prescribed producer calls, the original root with the Fraction backend, and the final source-bound composition of the four parent covers. The four original root OPEN records were matched to complete parent covers; the final receipt reports `effective_open_count = 0`. This is the negative-diagonal finite cover **conditional on retained upstream analytic and complete-X conclusions**. It did not rerun their entire dependency chain on a new machine or introduce an independent verifier implementation.

The v1.0.2 replay supplement keeps the sealed executed plan and drivers, the final receipt archive and subsequent audits separately identified. A returned receipt hash or a successful download is a file identity check, not a new mathematical replay. Four inherited complement receipts intentionally have intermediate OPEN paths.

A separate [public-archive assembly preflight](../provenance/v102_assembly_preflight/README.md) checked both full compressed archive hashes, extracted 706 selected pinned members into a new directory, and reproduced the 570-job, 566-target dependency plan. It did not run the producers or fully extract the archives; the broader fresh-machine theorem replay remains unclaimed.

## Lean scope

The first-phase project cold-rebuild result already recorded in v1.0.1 remains: 634 product modules, three additional modules and 47 named axiom checks, with third-party caches reused and supplemented. The separate B366 second-phase archive is **source only**: 1,452 accepted source modules and four separately identified support sources. It is not a new full-project build. The final Lean equality still assumes `XGlobalSafety` and `RootEndpointSafety`, and the large certificate trees are not claimed to be Lean-checked.

## Inherited certificate assets

The 24 original proof assets remain fixed under [v1.0.0](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0), totaling 4,494,382,372 bytes. Their existing URLs and SHA-256 values in [release-assets.json](../manifests/release-assets.json) remain valid; they are not reuploaded under v1.0.2. GitHub's automatic source ZIP does not include them. The dated replay records and new manuscript files are additional objects, with their own release identities.

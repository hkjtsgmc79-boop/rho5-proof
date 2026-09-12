# RHO5 v1.0.1 — revised paper, supplementary index and build evidence

**Qianli Ma · Chao Wu** · Zhejiang University; Qianli Ma also affiliated with WUJIE AI.

## Read the new documents

- [Article PDF · 56 pages](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.1/rho5_manuscript.pdf)
- [Supplementary index PDF · 7 pages](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.1/RHO5_SUPPLEMENTARY_INDEX.pdf)
- [Article, index and typesetting source](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.1/rho5-paper-v1.0.1.zip)
- [English verification guide](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.1/docs/VERIFY.md) · [中文验证教程](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.1/docs/VERIFY.zh-CN.md)

The expanded manuscript explains the global reductions, boundary cases, source-cover composition and an actual exact certificate. Both PDFs include the current author affiliations/emails and acknowledgment wording.

## Cold-rebuild record

The frozen first-phase Lean product has passed a project cold rebuild: **634 product modules, three additional modules, and 47 named axiom checks**. The accepted route used an explicit dependency-order driver, with third-party caches reused and supplemented. The original packaged Lake command failed in the cold state. [Full scope and evidence](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.1/docs/LEAN_COLD_REBUILD.md).

The sharp Lean equality still assumes `XGlobalSafety` and `RootEndpointSafety`. This is not a complete unconditional Lean proof, a fresh-machine build of every dependency, or a new all-components mathematical replay. The original receipt archive is included as an attachment; it is evidence, not a standalone rebuild kit.

## Original certificates — unchanged and directly accessible

The **24 original assets** remain frozen under [v1.0.0](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0). This release indexes them without duplicating the **4.494 GB** archive collection. Their original download URLs and SHA-256 values remain valid. Existing verified downloads can be reused.

- [Complete download table and computing requirements](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.1/docs/DOWNLOADS.md)
- [Original asset manifest](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/release-assets.json) · [Original SHA-256 manifest](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/SHA256SUMS.txt)
- [Lean source · 6.43 MB](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5-lean-phase-one.zip)
- [Real 54-leaf example · 18.29 MB](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/download/v1.0.0/rho5-final-anchor-example.zip)

Use `python3 scripts/fetch.py --list` or `--group sample` from the v1.0.1 checkout. GitHub's automatic source ZIP does not include the large certificate assets. The current release index separates new document/evidence assets from inherited certificates.

Zenodo archival will follow. [Full change history](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.1/CHANGELOG.md).

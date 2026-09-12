# The exact growth factor for complete pivoting on real 5 × 5 matrices

**Qianli Ma · Chao Wu**  
Zhejiang University; Qianli Ma also affiliated with WUJIE AI  
Contact: [qianli.ma@zju.edu.cn](mailto:qianli.ma@zju.edu.cn)

This repository accompanies the computer-assisted proof of

\[
\rho_5^{\mathbb R}=\alpha=4.132517078632472854223346853277\ldots.
\]

The algebraic constant and attained lower bound are due to Chen, Edelman and Urschel. The accompanying paper establishes the matching global upper bound, allowing every legal pivot tie and singular termination.

The release combines **partial Lean formalization**, **exact computational certificates**, and **Python/C++ verification source**. It does not claim a complete Lean proof of the global bound or formally verified Python/C++ executables.

| Start here | What you obtain |
|---|---|
| [Step-by-step verification](docs/VERIFY.md) | Fixed-version build, small real example, and complete-certificate routes |
| [Downloads and computing requirements](docs/DOWNLOADS.md) | Exact file sizes, checksums, measured times and planning allowances |
| [Proof and trust map](docs/PROOF_MAP.md) | What Lean proves, what remains external, and how the components fit |
| [Paper](paper/rho5_manuscript.pdf) | The mathematical argument and reproducibility scope |
| [Supplementary index](paper/RHO5_SUPPLEMENTARY_INDEX.pdf) | S1–S8 proof objects, original filenames and verifier entry points |
| [Release v1.0.0](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0) | Original source bundle and certificate assets, including large B archives |
| [中文导读](README.zh-CN.md) | 中文验证路线与范围说明 |

## Two independent starting points

**Lean analytic development.** The `lean/` project contains 646 canonical source modules (35.03 MB); the default entry loads 634. The original downloadable source ZIP is about 6.43 MB. Lean and mathlib are pinned, and caches are obtained separately.

```sh
cd lean
elan toolchain install leanprover/lean4:v4.30.0
lake exe cache get
lake build +Rho5.PhaseOne:olean
```

**A real exact certificate.** The final 54-leaf anchor is an approximately 18.3 MB, standard-library Python example. Start from the repository root:

```sh
python3 scripts/fetch.py --group sample
```

Then follow [the anchor walkthrough](docs/VERIFY.md#3-a-small-real-certificate). Its successful result covers that named anchor, not the whole B domain.

## What has been checked

The published first-phase Lean assembly has successful cached builds of its new entry, audit and usage examples, with recorded standard-axiom checks. The actual alpha constant, its attainment and key analytic/source reductions are included. The sharp equality remains conditional on `XGlobalSafety` and the original `RootEndpointSafety`; those premises are displayed in the public theorem types.

The computational archives preserve the original exact verification code, input data, source bindings and recorded component acceptances. Reproducing the entire proof requires the necessary component checks and the final source-cover composition. A matching file hash or an old PASS receipt alone is not a new mathematical verification.

**This publication operation does not constitute a new-machine Lean cold build or a new all-components mathematical replay.** The guide records the existing entry points and the remaining portability limitations explicitly. No search campaign or GPU is needed to use the documented exact verification paths.

## Repository layout

- `lean/`: canonical first-phase project, fixed dependencies, original scope and build documentation.
- `analytic/foundations/`: retained exact constant, candidate and foundational source materials.
- `verifiers/`: byte-identical source mirrors from named certificate archives for online inspection. Run each verifier with its original archive inputs.
- `manifests/`: release asset identities and source-mirror provenance.
- `scripts/`: standard-library downloader with resumable downloads, SHA-256 checks and multipart reconstruction.
- `paper/` and `docs/`: paper, supplement, instructions and scope map.

Large certificates are Release attachments and are not included by GitHub's automatic “Source code” ZIP. Use the download manifest and helper. The original archives retain historical filenames and scope labels; later source-bound covers discharge the original remaining leaves.

## Citation and versions

Use the fixed release and source commit when citing these materials; see [CITATION.cff](CITATION.cff). GitHub publication precedes Zenodo archival. No Zenodo DOI is claimed for this release at present. Existing third-party notices remain applicable; the repository does not assign a new blanket licence to the collected historical materials.

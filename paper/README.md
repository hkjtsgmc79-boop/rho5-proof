# RHO5 paper and supplementary index — v1.0.2

**Qianli Ma and Chao Wu.** The exact maximum growth factor for complete pivoting on real 5 × 5 matrices.

The published version DOI is <https://doi.org/10.5281/zenodo.23057256>. This package contains the same 88-page article PDF and 9-page supplementary-index PDF deposited in that Zenodo record, plus their TeX sources, the bibliography, a preserved BBL file, and selected exact inputs used to illustrate the proof. The previous v1.0.1 PDFs remain separately archived at <https://doi.org/10.5281/zenodo.22727368>.

- `rho5_manuscript.pdf` / `.tex`: article and source.
- `RHO5_SUPPLEMENTARY_INDEX.pdf` / `.tex`: supplementary index and source.
- `references.bib`, `rho5_manuscript.bbl`: bibliography inputs.
- `data/`: selected small examples and historical first-phase Lean build evidence, retained from v1.0.1.
- `archive/v1.0.0/`: historical reader note; current claims are in the v1.0.2 article and index.
- `SHA256SUMS.txt`: hashes of every packaged file except the manifest itself.

To typeset, run `tectonic rho5_manuscript.tex` and `tectonic RHO5_SUPPLEMENTARY_INDEX.tex` in this directory with a suitable TeX environment. Typesetting is separate from exact certificate verification.

The large frozen certificates and their original verifier code remain at <https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0>, indexed by the fixed v1.0.1 release <https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.1>. A separate v1.0.2 GitHub release documents the paper revision and added replay evidence. The recorded first-phase Lean rebuild is partial; the article does not claim an unconditional Lean proof of its main theorem.

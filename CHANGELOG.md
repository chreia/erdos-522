# Changelog

## v1.1.0 (2026-09-25)

- **Theorem 1.3.** The constant of the almost-sure rate is lowered from $2000\log2$ to $128$: almost surely, $\limsup_n(\log n)|\nu_n(1)/n-1/2|\le128$. The proof takes the annular width $K_N=\lfloor\log N/128-\log\log N\rfloor$ and the secant radii of Lemma 2.4 with $\eta=1/K_N$. The Lean theorems `ae_rademacher_logarithmic_root_rate` and `ae_rademacher_logarithmic_root_rate_eventually` state the new constant.
- **Proofs.** Section 6 proves Theorem 1.1 once, and Corollary 1.2 is its case $x=0$, in the paper and in Lean. The matching step uses disjoint disks about roots with a large derivative (Lemma 5.4), as the formalization does. Theorem B.1 bounds the clipping error through Hölder's inequality, which improves the exponents of Theorem 3.1 and Lemma 4.5, and a new Lean module proves this form. Section 7 is one proof under the hypotheses (H1)–(H5).
- **Presentation.** The paper is shorter (145 pages): parameter tables at the start of the proofs of Theorems 1.1 and 1.3, a reader's guide, rotation and reflection notation for the covariance matrices, tables for the hypotheses (H1)–(H5) and for the constants of Appendix A, and a short Section 10 on numerical methods. The log–log fits formerly in Section 10 are in `numerics/publication/STATISTICS.md`.
- **DOI.** The paper has the DOI [10.5281/zenodo.22970145](https://doi.org/10.5281/zenodo.22970145).

## v1.0.0 (2026-09-25)

Initial release.

- **Paper.** *Almost-Sure Radial Laws for Nested Random Polynomials and Erdős Problem #522*, 151 pages, with its LaTeX source, bibliography and figures.
- **Formalization.** Lean 4 proofs of Theorem 1.1 and Corollary 1.2 for five coefficient distributions, Theorem 1.3, and the results of Section 8, on Lean v4.34.0 and Mathlib `5ed2965`. The 45 main theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Numerics.** Scripts, seeds and summary data for the numerical figures (Figures 6, 7, 9 and 10) and Tables 8 and 9, whose methods are described in Section 10.
- **Continuous integration.** Every push builds the formalization and checks the axioms of the main theorems.

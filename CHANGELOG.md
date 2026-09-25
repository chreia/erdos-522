# Changelog

## v1.0.0 (2026-09-25)

Initial release.

- **Paper.** *Almost-Sure Radial Laws for Nested Random Polynomials and Erdős Problem #522*, 151 pages, with its LaTeX source, bibliography and figures.
- **Formalization.** Lean 4 proofs of Theorem 1.1 and Corollary 1.2 for five coefficient distributions, Theorem 1.3, and the results of Section 8, on Lean v4.34.0 and Mathlib `5ed2965`. The 45 main theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Numerics.** Scripts, seeds and summary data for the numerical figures (Figures 6, 7, 9 and 10) and Tables 8 and 9, whose methods are described in Section 10.
- **Continuous integration.** Every push builds the formalization and checks the axioms of the main theorems.

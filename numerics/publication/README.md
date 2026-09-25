# Numerical figures and tables

This folder reproduces the numerical figures (Figures 6, 7, 9 and 10) and Tables 8 and 9 of the paper from summary data. Their methods are described in Section 10. The computations illustrate the theorems. No proof uses them.

| Paper | Output | Source data |
|---|---|---|
| Figure 6 | `figures/annulus.pdf` | `data/annulus.csv` |
| Figure 7 | `figures/small-derivative.pdf` | `data/small-derivative.csv`, `data/bootstrap-fits.json` |
| Figure 9 | `figures/root-matching.pdf` | `matching.npz` |
| Figure 10 | `figures/radial-profile.pdf` | `data/radial-profile.csv`, `data/sequence-statistics.npz` |
| Table 8 | `degree_coverage` in `metadata.json` | `data/sequence-statistics.npz` |
| Table 9 | `data/bootstrap-fits.json` | `data/sequence-statistics.npz` |

## Commands

With Python 3.14, NumPy 2.5.1 and Matplotlib 3.11.1 (`pip install -r requirements.txt`), run from the repository root:

```sh
python3 numerics/publication/prepare.py   # tables, plotted data and metadata.json
python3 numerics/publication/render.py    # figures and rendering.json
```

`prepare.py` reads only `data/sequence-statistics.npz`. `render.py` reads the plotted data in `data/`, `metadata.json` and `matching.npz`. With the versions above, both scripts reproduce the committed files byte for byte, and `rendering.json` records the SHA-256 hash of every input and output. `prepare.py` also writes `data/diagnostic-scaling.csv`, `data/occupation-means.csv`, `data/logarithmic-means.csv`, `data/blob.csv` and `data/small-derivative-supplement.csv`, which back statements in Section 10.

## Seeds

- **Coefficients.** Sequence `s` uses the signs `numpy.random.Generator(numpy.random.PCG64(s)).choice(np.array([-1, 1], dtype=np.int8), 125001)`, for `s = 522000, ..., 522099`. Every degree of a sequence uses a prefix of the same signs.
- **Bootstrap.** 2,000 multinomial draws with base seed 522987. Each cohort has its own stream `numpy.random.SeedSequence([522987, group])`: group 1 for the 77 root sequences, 2 for the 100 FFT sequences, 3 for the endpoint sequences, and 4 for the 78 complete blocks at degree 1,000.
- **Single sequences.** Figure 9 and panel (c) of Figure 10 use seed 522000. Figures 6, 7 and panels (a) and (b) of Figure 10 use the 77-sequence common root cohort.

`metadata.json` lists the seeds of every cohort.

## Samples and conventions

- **Roots.** The roots at the five base degrees 1,000, 3,000, 10,000, 30,000 and 100,000 were computed with MPSolve and three Newton refinements. The completed base samples number 92, 92, 92, 91 and 77. Every completed sample is retained, independently of its root counts.
- **Counts.** Root counts keep multiplicities. Exact roots at ±1 count at radius one. Other roots within `1e-9` of the unit circle get separate lower and upper counts, and `metadata.json` records the resulting sensitivity. These intervals are not certified enclosures.
- **Residuals.** The normalized residual is `|f_N(z)| / sum_k |z|^k`. Its maximum at each base degree is in Table 8, and `data/residuals-by-degree.csv` gives it for every degree. That file is output of the root computations, and neither script regenerates it.
- **Uncertainty.** Bootstrap draws resample whole coefficient sequences, so all degrees and radii of a sequence stay together. Bands are pointwise 95% percentile intervals.
- **Root matching.** `matching.npz` holds the roots of one sequence at degrees 1,000, 1,210 and 1,421, and the counts at all 422 degrees of that block. The links in Figure 9 are minimum-distance assignments. They are empirical and do not certify an analytic matching. `matching.json` describes the arrays and the residual checks.

## Files

- `prepare.py`: bootstrap summaries, plotted tables and `metadata.json`.
- `render.py`: vector figures from the plotted data.
- `metadata.json`: seeds, cohorts, normalizations, sample coverage and figure inputs.
- `rendering.json`: figure sizes and SHA-256 hashes of the renderer, its inputs and its outputs.
- `data/sequence-statistics.npz`: per-sequence summaries (radial profiles, annular counts, derivative counts, block observations and FFT statistics). It opens with `allow_pickle=False`, and missing values are NaN.
- `data/*.csv`, `data/bootstrap-fits.json`: plotted estimates, intervals and fitted slopes, the Section 10 diagnostics, and the residuals by degree.
- `matching.npz`, `matching.json`: the root-matching data.
- `figures/`: the four figures of the paper, as PDF.

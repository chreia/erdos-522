# Paper source

The LaTeX source of *Almost-Sure Radial Laws for Nested Random Polynomials and Erdős Problem #522*. The compiled paper is [`../Erdos522.pdf`](../Erdos522.pdf).

With TeX Live 2026, build from this folder:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The bibliography is in `references.bib`, and the processed bibliography `main.bbl` is included for builds without BibTeX. The four numerical figures are read from [`../numerics/publication/figures/`](../numerics/publication/figures), and the explanatory figures from `figures/explanatory/`. The scripts that draw them are in [`../numerics/publication/`](../numerics/publication) and [`figures/explanatory/src/`](figures/explanatory/src).

The paper, its source and its figures are licensed under [CC BY 4.0](LICENSE). The scripts in `figures/explanatory/src/` are licensed under the [Apache License 2.0](../LICENSE).

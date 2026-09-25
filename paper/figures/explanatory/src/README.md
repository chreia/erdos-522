# Explanatory figures

These scripts draw the explanatory figures of the paper into the parent folder.

| Paper | PDF | Script | Data |
|---|---|---|---|
| Figure 1 | `radial-density.pdf` | `radial_density.py` | `data/polar-hist.npz` |
| Figure 2 | `proof-map.pdf` | `proof_map.py` | the aux file of a paper build |
| Figure 3 | `jensen-secants.pdf` | `jensen_secants.py` | `data/jensen.npz` |
| Figure 5 | `angular-logarithm.pdf` | `angular_logarithm.py` | `data/angular-means.npz`, signs of seed 522000 |
| Figure 8 | `phase-portrait.pdf` | `phase_portrait.py` | signs of seed 522000 |

Figure 4, the tilted mean, is drawn in pgfplots in `../tilted-mean-plot.tex`.

With Python 3.14, NumPy, Matplotlib 3.11, SciPy, cmocean and fontTools (tested with Python 3.14.6, NumPy 2.5.1, Matplotlib 3.11.1, SciPy 1.18.1, cmocean 4.0.3 and fontTools 4.66.0), build the paper once (see [`paper/README.md`](../../../README.md)) and run from this folder:

```sh
python3 radial_density.py
python3 proof_map.py        # reads paper/build/main.aux, or pass another aux file
python3 jensen_secants.py
python3 angular_logarithm.py
python3 phase_portrait.py
```

- **Data.** `data/polar-hist.npz` bins the zeros of the 77 sequences of degree $10^5$ (the common root cohort of [`numerics/publication/metadata.json`](../../../../numerics/publication/metadata.json)) into 1,440 angles and 320 values of $N(|z|-1)$ on $[-8,8]$. For seed 522000, `data/jensen.npz` holds $J_N(1+x/N)$ and $\nu_N(1+x/N)$ at $N=10^5$ for $|x|\le10$, and `data/angular-means.npz` holds $J_N(1+x/N)-\log\sigma_N(1+x/N)+\gamma/2$ at $N=10^3,10^4,10^5$ for $|x|\le6$. Both are computed from the roots by Jensen's formula. The signs of seed 522000 are read from [`numerics/publication/matching.npz`](../../../../numerics/publication/matching.npz).
- **Proof map.** `proof_map.py` reads the numbers of the results it names from the aux file, so after a renumbering, build the paper, run the script, and build again.
- **Fonts.** `paperstyle.py` finds the Latin Modern fonts through `kpsewhich` and caches TrueType copies in `~/.cache/erdos522-latin-modern`.
- **Rasters.** The ring in Figure 1, the phase portrait, and the heat map in Figure 5 are raster images inside vector PDFs.
- **Versions.** The committed PDFs of Figures 1, 5 and 8 were drawn with Matplotlib 3.10.9. Redrawn with Matplotlib 3.11.1, they differ only by one-pixel shifts of text and by anti-aliasing.

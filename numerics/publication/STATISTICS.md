# Statistics behind the numerical figures

This note records the log–log fits and the comparison of each statistic with its reference curve, for the figures of the section "Numerical methods" of the paper. That section, and `README.md`, describe the samples, the root solvers, the residual check, the boundary count sensitivity and the FFT grid check. The limits that hold with probability one follow from the proofs of the paper, and these proofs do not use the computations. The figures describe measurements at finite degrees, and the fitted slopes describe only the measured range.

## Samples and uncertainty

We use 100 independent sequences of random signs at the degrees $N=1000$, $3000$, $10000$, $30000$ and $100000$, and the block length is $\lfloor N^{7/8}\rfloor$. For the profile and root-count comparisons we use the 77 sequences that were completed at all five base degrees, while the angular comparisons use all 100 sequences. The bootstrap uses 2000 whole-sequence draws, and the bands and intervals are pointwise 95% percentile intervals.

## Log–log fits

Representative log–log fits across the measured degrees or thresholds:

| Statistic | Slope | 95% interval |
| --- | ---: | ---: |
| $\operatorname{Var}A_1$ at $r=1$ | $-1.053$ | $[-1.130,-0.980]$ |
| Centered log-integral mean square at $r=1$ | $-0.975$ | $[-1.052,-0.903]$ |
| Annular small-derivative fraction versus $L$ | $-2.293$ | $[-2.301,-2.285]$ |
| Global small-derivative fraction versus $L$ | $-0.687$ | $[-0.688,-0.686]$ |
| Larger-degree endpoint change | $0.878$ | $[0.873,0.883]$ |
| Endpoint change after removing degree drift | $0.460$ | $[0.364,0.559]$ |

The first two rows use the doubled angular grids and five base degrees. The derivative rows use $N=10^5$ and $L=2,4,8,16$. The endpoint rows use 27 common sequences at the four larger base degrees.

## Radial mass and logarithmic concentration

We compare the empirical profile $\widehat\Phi_N(x)=\nu_N(1+x/N)/N$ of the radial-profile figure with $\Phi(x)$, and the outside-annulus count with $2\log2/K$ and with

$$
1-\{\Phi(K)-\Phi(-K)\}=\frac1K-\frac{2}{e^{2K}-1},\qquad K=2,4,8,16,32.
$$

We also compare the occupation means with $1-e^{-t^2}$, and we fit the variance of occupation and the centered logarithmic mean square over the available degrees (first two rows of the table above).

The centered logarithmic mean square is that of $\widehat I_N(1+x/N)+\gamma/2$, where $\widehat I_N(r)$ is the average of $\log|f_N/\sigma_N(r)|$ over the shifted FFT grid on $|z|=r$, which approximates $J_N(r)-\log\sigma_N(r)$.

## Small derivatives

In the threshold comparison we use $L=2,4,8,16$ in the $K=2$ annulus and include the two thin sectors around the real axis, while larger thresholds and retained-angle counts provide supplementary comparisons. We compare the finite-range slope with the small-threshold power $-4$, and the global counts show the effect of the annular restriction. At $N=10^5$, the supplementary retained-angle fit over $L=16,32,64,128$ has slope $-3.852$ and interval $[-4.476,-3.450]$. Over the primary threshold range the slope is close to $-2.3$.

For the Gaussian local comparison, we set

$$
I(x)=\int_0^1e^{2xt}\,\mathrm dt,
\qquad B(x)=\int_0^1t e^{2xt}\,\mathrm dt,
\qquad V(x)=\int_0^1t^2e^{2xt}\,\mathrm dt-\frac{B(x)^2}{I(x)}.
$$

The Gaussian calculation then integrates

$$
\frac{2V(x)}{I(x)}
\left\{1-\left(1+\frac{L^{-2}}{V(x)}\right)e^{-L^{-2}/V(x)}\right\}
$$

over the annulus, for comparison with the data for polynomials with random signs.

## Localization

The measured amplitude is $a=15e^4\sqrt{\lfloor N^{7/8}\rfloor\log N}$, which is that of the appended-tails lemma of the paper (Lemma "Appended tails") with $2$ in place of $K$. We use the two adaptive radii $2a/|f_N'(\alpha)|$ and $2aL/|f_N'(\alpha)|$, and the uniform radius $2aL/N^{3/2}$. For containment in the auxiliary $K=2$ annulus of the proof we use that lemma with $4$ in place of $K$, and at the same block length its amplitude and radii are then $e^4$ times larger.

For the radius $2a/|f_N'(\alpha)|$ above and each $L$, we take its median over the roots with $\bigl||\alpha|-1\bigr|\le2/N$ and $|f_N'(\alpha)|\ge N^{3/2}/L$, and we average these medians over 77 common samples. These averages lie between $3.8\times10^3/N$ and $7.9\times10^3/N$, and every finite-constant disk that we recorded contains more than one computed root.

## Degree blocks

At $N=1000$ the maxima use every intermediate polynomial in each of the 78 complete blocks, while at the larger degrees we obtain endpoint changes from the endpoint samples. From the midpoint samples we also obtain three-point maxima. Within the count sensitivity described in the paper, the endpoint and three-point maxima are lower bounds for the full-block maximum. We measure both the uncentered changes and the changes after subtracting the degree drift. For the endpoint changes we use 27 common sequences at the larger degrees and 78 complete blocks at $N=1000$.

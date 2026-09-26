# Lean formalization

This directory contains the Lean 4 formalization of the paper [*Almost-Sure Radial Laws for Nested Random Polynomials and Erdős Problem #522*](../Erdos522.pdf), version 1.1.0. It uses Lean 4.34.0 and Mathlib at revision [`5ed2965`](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435). Every declaration lives in the namespace `Erdos522`, and `import Erdos522` brings the main theorems into scope.

## Building and checking

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get                         # download the compiled Mathlib
lake build                                 # compile the formalization
lake env lean checks/MainTheorems.lean     # print the main theorems and check their axioms
lake env leanchecker --fresh Erdos522.All  # replay every proof in the kernel
```

The build treats every warning as an error. [`checks/MainTheorems.lean`](checks/MainTheorems.lean) prints the full statement of each of the 45 main theorems and fails unless each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The last command replays, in a fresh environment, every declaration that [`Erdos522.All`](Erdos522/All.lean) depends on, through the Lean kernel alone.

## The results and their declarations

Every declaration below is proved, with only the three axioms above. [CORRESPONDENCE.md](CORRESPONDENCE.md) repeats this table and compares the formal and informal proofs.

| Result | Coefficients | Declaration |
|---|---|---|
| Theorem 1.1, radial law | Rademacher | [`radial_profile_compact_uniform_prefixes`](Erdos522/Probability/RadialProfile.lean#L57) |
| | Steinhaus | [`steinhaus_radial_profile_compact_uniform_prefixes`](Erdos522/Probability/SteinhausRadialProfile.lean#L55) |
| | real Gaussian | [`gaussian_radial_profile_compact_uniform_prefixes`](Erdos522/Probability/GaussianRadialProfile.lean#L55) |
| | complex Gaussian | [`circularGaussian_radial_profile_compact_uniform_prefixes`](Erdos522/Probability/CircularGaussianRadialProfile.lean#L55) |
| | bounded symmetric | [`bounded_symmetric_radial_profile_compact_uniform_of_nontrivial`](Erdos522/Probability/SymmetricCoefficientLaws.lean#L65) |
| Corollary 1.2, Erdős #522 | Rademacher | [`erdos_522`](Erdos522/Probability/RademacherZeroDistribution.lean#L25) |
| | Steinhaus | [`steinhaus_zero_distribution`](Erdos522/Probability/SteinhausRadialProfile.lean#L66) |
| | real Gaussian | [`gaussian_zero_distribution`](Erdos522/Probability/GaussianRadialProfile.lean#L66) |
| | complex Gaussian | [`circularGaussian_zero_distribution`](Erdos522/Probability/CircularGaussianRadialProfile.lean#L66) |
| | bounded symmetric | [`bounded_symmetric_zero_distribution_of_nontrivial`](Erdos522/Probability/SymmetricCoefficientLaws.lean#L79) |
| Theorem 1.3, logarithmic rate | Rademacher | [`ae_rademacher_logarithmic_root_rate_eventually`](Erdos522/Probability/EventualLogarithmicRootRate.lean#L60) |
| Logarithmic moments (17) | | [`LogMoments.uniform_logarithmic_moments`](Erdos522/Probability/LogMoments/UniformLogarithmicMoments.lean#L69) |
| Proposition 8.1, sparse degrees | | [`admissible_fixed_sparse_degree_scales`](Erdos522/Limits/SparseDegreeParameters.lean#L96), [`admissible_sparse_degree_scales`](Erdos522/Limits/SparseDegreeParameters.lean#L41), [`two_lt_of_occupation_summability`](Erdos522/Limits/SparseDegreeParameters.lean#L107), and for the radial laws [`ae_radial_profile_via_fixed_degree_scales`](Erdos522/Probability/RealPowerRadialInterpolation.lean#L156), [`ae_radial_profile_via_real_power_degrees`](Erdos522/Probability/RealPowerRadialInterpolation.lean#L148) |
| Proposition 8.3, weighted variance profile | | [`log_weightedRadialSigmaWithConstant_profile_compact_uniform`](Erdos522/Probability/WeightedConstantTerm.lean#L91), [`deriv_weightedLogVarianceProfile`](Erdos522/Analysis/WeightedProfileDerivative.lean#L163), [`deriv_weightedLogVarianceProfile_zero`](Erdos522/Analysis/WeightedProfileDerivative.lean#L170) |
| Proposition 8.5, weighted polynomials with random signs | | [`integral_weighted_logarithmic_moment_le`](Erdos522/Probability/WeightedLogarithmicMoments.lean#L96), [`integral_weighted_normalized_energy`](Erdos522/Probability/WeightedLogarithmicMoments.lean#L108), and for any constant coefficient $c_0\ne0$ [`weighted_logarithmic_moments_with_constant`](Erdos522/Probability/WeightedConstantTerm.lean#L180), [`integral_weighted_normalized_energy_with_constant`](Erdos522/Probability/WeightedConstantTerm.lean#L196) |
| Corollary 8.2, nearby circles | | [`fixed_level_nearby_circle_sublevel_counts_summable`](Erdos522/Probability/NearbyCircleSublevelCounts.lean#L50) |

Each declaration states the result in its row, with four differences in form.

- **Theorem 1.3** is stated in eventual form: almost surely, for every $c>128$, eventually $(\log n)\left|\nu_n(1)/n-1/2\right|\le c$. This is equivalent to the bound on the limit superior, since $\limsup_n a_n\le L$ holds exactly when $a_n\le c$ for all large $n$, for every $c>L$.
- **The bound (17)** is proved in a stronger form. It allows complex unit vectors of coefficients, with its own absolute constant.
- **Proposition 8.1.** The declarations prove the conditions on $q$ and on the powers. The radial laws for all degrees, obtained through the degrees $\lfloor j^q\rfloor$, are proved at each fixed $x$, with a null set that depends on $q$ and $x$.
- **Corollary 8.2** is proved in a stronger form. It holds for every $\kappa>0$.

The limiting profile is [`kacRadialProfile`](Erdos522/Analysis/RadialProfileRegularity.lean#L24), the derivative of $\frac12\log\int_0^1e^{2xt}\thinspace dt=\frac12\log\bigl((e^{2x}-1)/(2x)\bigr)$. The theorems [`kacRadialProfile_zero`](Erdos522/Analysis/RadialProfileRegularity.lean#L26) and [`kacRadialProfile_eq`](Erdos522/Analysis/KacRadialProfile.lean#L22) give its value $1/2$ at $x=0$ and its closed form $e^{2x}/(e^{2x}-1)-1/(2x)$ elsewhere. The file [CORRESPONDENCE.md](CORRESPONDENCE.md) compares the formal and informal proofs in detail, and explains how the proof of Theorem 1.3 reaches the constant $128$ with the annular width $\lfloor\log N/128-\log\log N\rfloor$.

The file [`Erdos522/Bridge/FormalConjectures.lean`](Erdos522/Bridge/FormalConjectures.lean) proves the statement [`erdos_522`](Erdos522/Bridge/FormalConjectures.lean#L238) of [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (`FormalConjectures/ErdosProblems/522.lean`), with its definitions and statement copied verbatim, from `erdos_522_of_independent_coins`.

## Conventions

- The polynomial `polynomialPrefix ξ c N` takes the coefficients with indices $0$ through $N$ from one infinite sequence, so that every degree is built from the same coefficients.
- `closedZeroCount P r` counts the roots of $P$ in the closed disk $|z|\le r$ with multiplicity. For the zero polynomial it is $0$.
- In every limit the denominator is the nominal degree $N$.

## Layout

| Folder | Files | Contents |
|---|---|---|
| [`Erdos522/Basic`](Erdos522/Basic) | 4 | polynomial prefixes and zero counts |
| [`Erdos522/Analysis`](Erdos522/Analysis) | 93 | Jensen secants and the variance profiles |
| [`Erdos522/Probability`](Erdos522/Probability) | 279 | occupation, jets, logarithms, local counts, tails, and the main theorems |
| [`Erdos522/Stability`](Erdos522/Stability) | 13 | Rouché's theorem, isolation of zeros and root matching |
| [`Erdos522/Limits`](Erdos522/Limits) | 17 | blocks of degrees and the passage from sparse to all degrees |
| [`Erdos522/Bridge`](Erdos522/Bridge) | 1 | the statement of Erdős #522 in google-deepmind/formal-conjectures |
| [`checks`](checks) | 1 | the statements and axioms of the main theorems |
| [`vendor`](vendor) | | two libraries by other authors, see below |
| [`third_party`](third_party) | | the license of the adapted file `PolynomialRouche.lean`, see below |

[`Erdos522.lean`](Erdos522.lean) imports the main theorems, and [`Erdos522/All.lean`](Erdos522/All.lean) adds the supplementary results and is the target of the kernel replay. `lake build` compiles both.

## Third-party code

The directory [`vendor`](vendor) contains two libraries by other authors, each under the Apache License 2.0 and ported to Lean 4.34:

- [ProbabilityApproximation](https://github.com/Polarnova/ProbabilityApproximation), by Asher Yan, for Bentkus's multivariate normal approximation.
- [SLT](https://github.com/YuanheZ/lean-stat-learning-theory), by Yuanhe Zhang, Jason D. Lee, Fanghui Liu and contributors, for the Hanson–Wright inequality.

The file [`Erdos522/Stability/PolynomialRouche.lean`](Erdos522/Stability/PolynomialRouche.lean) is adapted from [hex-roots-mathlib](https://github.com/leanprover/hex-roots-mathlib) (Lean FRO, Apache License 2.0). The [vendor README](vendor/README.md) and the [NOTICE](../NOTICE) file give the details.

## License

Copyright 2026 Sebastien Kawada. Released under the [Apache License 2.0](../LICENSE). The third-party code keeps its own copyright notices.

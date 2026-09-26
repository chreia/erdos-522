# The paper and the formalization

This note complements Appendix C of the [paper](../Erdos522.pdf). It lists the formal declaration of each result, records the four places where a formal statement differs in form from the paper, describes the formal conventions, and compares the formal and informal proofs. Numbers of theorems and equations refer to the paper, and declarations belong to the namespace `Erdos522`.

## Declarations

Every declaration below is proved, and depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

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


## The logarithmic rate

The declaration `ae_rademacher_logarithmic_root_rate_eventually` states that almost surely, for every $c>128$, eventually $(\log n)\left|\nu_n(1)/n-1/2\right|\le c$. This is Theorem 1.3, since for a real sequence $(a_n)$ and a real number $L$ the bound $\limsup_n a_n\le L$ holds exactly when $a_n\le c$ for all large $n$, for every $c>L$. The formalization also contains `ae_rademacher_logarithmic_root_rate`, which states the same bound with Mathlib's real limit superior. That notion assigns the value $0$ to a sequence that is not bounded above, and the eventual form, which bounds the sequence directly, is the faithful statement of the theorem.

## The constant 128

The formal proof of Theorem 1.3 uses the annular width $K_N=\lfloor\log N/128-\log\log N\rfloor$ (`logarithmicAnnularWidth`) and the secant radii $1\pm(K_N-1)/N$ and $1\pm K_N/N$ (`radialUnitGapRadii`), which is Lemma 2.4 with $\eta=1/K_N$. The secants bound the fraction of roots outside the annulus by $1/(K_N-1)+4(E_N+V_N)$, where $E_N$ is the logarithmic tolerance and $V_N$ the error of the variance profile (`radial_mass_le_kac_profile_gap_bound`, `radial_mass_le_finite_variance_unit_gap_bound`), and $(\log N)/(K_N-1)$ tends to $128$ (`tendsto_log_div_logarithmicAnnularWidth_sub_one`).
- The tolerance $E_N$ (`growingLogarithmicTolerance`) keeps the clipping threshold of Theorem B.1 at height $(1/32)\log N$ split into its terms, so that the occupation constant, which grows as $e^{9K}$, multiplies only $N^{-1/2}$ and $N^{-1/4}$. Its product with $\log N$ tends to zero (`tendsto_log_mul_growingLogarithmicTolerance`).
- The formalization compares the number of annular roots with a small derivative with the count threshold $N/(\log N)^2$ (`logarithmicCountThreshold`), with failure probability $N^{-3}+N^{-10}+C(K)N^{-7/16}(\log N)^8$ (`exists_annular_small_derivative_logarithmic_failure_constants`). The paper uses instead the split count bound $Z_KN^{15/16}\log N+Z'_KN^{17/32}(\log N)^2$. Both rows have cap $1/128$.
- A row with growth $e^{aK}$ in the width and decay $N^{-b}$ in the degree allows every width $K=c\log N$ with $c<b/a$, and $b/a$ is its cap. In the formalization the binding row is the mean number of detected mesh cells relative to the count threshold, $(K+1)^2e^{8K}(\log N)^3N^{-1/16}$, with cap $1/128$. The cap is attained through the correction $\log\log N$ in the width, which turns $e^{8K}$ into $N^{1/16}(\log N)^{-8}$ (`tendsto_logarithmicAnnularWidth_critical_factor`). The next strictest rows are the curvature margin of the root localization, $e^{3K}(\log N)N^{-1/32}$, with cap $1/96$, and the displacement margin $e^{2K}(\log N)^{1/2}N^{-1/32}$ and the Gaussian density in the mesh probability, $e^{6K}N^{-3/32}$, both with cap $1/64$.

## Conventions

- The polynomial prefix takes the coefficients with indices $0$ through $N$ from one infinite sequence.
- Its root count filters the multiset of complex roots by $|z|\le r$, so that it includes multiplicities and roots on the boundary.
- For the zero polynomial the count is zero, and in the limiting laws the denominator is the nominal degree $N$.
- For coefficient distributions with an atom at zero, the trailing zero runs are controlled separately.

## Statements

**Corollary 1.2 as the case $x=0$.** In the paper, Section 6 proves Theorem 1.1 once, and Corollary 1.2 is its case $x=0$, since $1+0/n=1$ and $\Phi(0)=1/2$. Section 7 carries out the same proof for the other distributions under the hypotheses (H1)–(H5), which Proposition 7.4 verifies. The formal unit-disk laws are derived in the same way: `erdos_522`, `steinhaus_zero_distribution`, `gaussian_zero_distribution`, `circularGaussian_zero_distribution` and `bounded_symmetric_zero_distribution_of_nontrivial` evaluate the radial law of their distribution at $x=0$, where `kacRadialProfile_zero` gives the value $1/2$. The declaration `erdos_522_of_harmonic_restriction` is a second formal proof for signs, through sparse unit-circle limits, and `erdos_522` does not use it.

**The logarithmic moment bound.** The bound (17) for random signs, the finite Rademacher case of Corollary 1.2 of Nazarov, Nishry and Sodin [NNS2013], is proved for every finite complex coefficient vector of unit norm and every $p\ge1$, with an absolute constant defined in the formalization in place of $C_*$. Its measure is the product of the distribution of $(\varepsilon_0,\dots,\varepsilon_N)$ with the uniform measure on the circle (`LogMoments.fourierMeasure`).

**Probability spaces.** For signs, the almost-sure statements live on the product space of one infinite sequence of fair coins, and the crossing bound is a statement about probabilities on that space.
- The formalization contains the unit-disk and compact-uniform radial laws for Steinhaus, standard real Gaussian and standard complex Gaussian coefficients.
- In the simultaneous and in the compact-uniform radial declarations, all real coordinates and all compact sets lie inside one almost-everywhere quantifier.
- The compact-uniform radial laws of all five coefficient distributions, and the unit-disk laws for signs and for bounded symmetric distributions, are also stated on any probability space that carries independent coefficients with the given distribution. For signs, this version takes independent fair coins (`erdos_522_of_independent_coins`).
- The general lemma `ae_iid_sequence_property` transfers every almost-sure statement in the same way.

**Bounded coefficients.**
- For bounded complex coefficients, central symmetry means that the distribution is invariant under $z\mapsto-z$, and nontriviality, which is the nondegeneracy of Theorem 1.1, means that the mass at zero is less than one.
- The formal statement allows any positive second moment and proves the normalization by a nonzero scalar.
- It is stated for distributions on $\mathbb C$. A real distribution is covered by its image in $\mathbb C$, which is again centrally symmetric, bounded and nontrivial.
- The formal trailing-run bound uses $\lceil D\log(N+1)\rceil$, and the proofs of Theorem 1.1 and Corollary 1.2 in Section 7 use $\lceil D\log N\rceil$. Both give a summable exceptional sequence and a normalized degree correction that tends to zero.

**Nearby circles.**
- The nearby-circle crossing theorem holds for every $\kappa>0$, and in particular in the range $0<\kappa\le1/12$ of Corollary 8.2.
- Both formulations use one summable exceptional sequence for the two circles at each fixed level and exponent.
- For levels that may vary with the degree, the declaration `nearby_circle_sublevel_counts_summable` gives the same conclusion, provided that they are eventually bounded by the maximal-tail amplitude of the block.

**Weighted profile.** As in Proposition 8.3, the formal weighted variance theorem allows every $\tau>-1/2$ and any fixed nonzero constant coefficient. Its conclusion concerns the logarithmic variance profile. For Proposition 8.5, the formal logarithmic moment bound holds for every $p\ge1$, with the constant of the formal bound (17) in place of $C_*$, and the declarations with the suffix `_with_constant` allow any fixed nonzero constant coefficient, as noted after Proposition 8.5.

**Sparse degree sequences.**
- For Proposition 8.1, the structure `AdmissibleSparseDegreeScales` collects the conditions of the construction on the exponent $q$ and the powers, as listed in its proof.
- The declarations `admissible_fixed_sparse_degree_scales` and `admissible_sparse_degree_scales` show that these conditions hold for $8/3<q<16$ with the fixed powers, and for every $q>2$ with the retuned powers, and `two_lt_of_occupation_summability` shows that the summability condition forces $q>2$.
- Along the degrees $\lfloor j^q\rfloor$, the radial law is `ae_admissible_sparse_radial_profile`.
- The all-degree laws `ae_radial_profile_via_fixed_degree_scales` and `ae_radial_profile_via_real_power_degrees` are proved through these sequences, with one null set for each $q$ and $x$.

Remarks 6.1 and 8.4 are not stated separately in the formalization.

## Proofs

**Normal approximation and Hanson–Wright.**
- For the normal approximation, the formalization uses Bentkus's theorem [Bentkus2005] with a symbolic universal constant, and the paper computes numerical constants from Raič's theorem [Raic2019].
- The formal Hanson–Wright estimates use an explicit moment-generating-function convention, and the paper's constant $c_{\mathrm{HW}}$ uses the convention of [RudelsonVershynin2013].
- Both choices make the probabilities of the exceptional events summable, with different constants and intermediate exponents, and with the same constant $128$ in the logarithmic rate.

**Complex Gaussian coefficients.**
- The energy and supremum estimates in Lean use two real Gaussian copies, and the proof of Proposition 7.4 uses a direct circular calculation, with smaller constants.
- Lean uses $\mathbb E\log|G|$ as the Gaussian logarithmic center, and the paper evaluates $\mathbb E\log|G|=-\gamma/2$. In both arguments the common center cancels from every radial secant.

**Matching, concentration and the general forms.**
- The paper and the formalization use the same disks in the matching step. Lemma 5.4 places a disk of radius $2a/d_0$ about each root $\alpha$ with $|P'(\alpha)|\ge d_0$, under the budget $4M_2a\le d_0^2$. Its conclusions are formal: $|P|\ge3a/2$ on the boundary circle (`regular_root_boundary_barrier`), exactly one root in the disk (`regular_root_count_ball`), the component of $\{|P|<a\}$ at $\alpha$ inside the disk (`regular_root_sublevel_component_subset_ball`), the separation of two regular roots (`regular_root_separation`, which gives $|\beta-\alpha|\ge2d_0/M_2\ge8a/d_0$), and the pairwise disjointness of the disks (`regular_root_family_disjoint`). Rouché's theorem on these disks gives the matching of Theorem 5.1 (`regular_root_family_matching`). The hypotheses on $P''$ differ slightly: the paper bounds $|P''|$ by $M_2$ on the closed disk of radius $4a/d_0$ about each root, and the formal family statements bound it on one convex region that contains the closed disks. In the proof of Theorem 1.1 both bounds hold on the disk $|z|\le1+(K+1)/N$.
- The concentration estimate of Theorem B.1 is proved formally in a general form, on an arbitrary probability space. In the paper the lower clipping error is bounded through Hölder's inequality with the exponents $2q$ and $2q/(2q-1)$, which gives the error term $\lambda(2Cq)^\beta(e^{-2T}+d_1+b)^{1-1/(2q)}$ and the Markov event for $W=\int|\log|X||^{2q}$. The declarations `logarithmic_integral_concentration_holder`, `logarithmic_integral_concentration_restricted_moments_holder` and `logarithmic_integral_concentration_of_restricted_moments_holder` state this form, with $\Lambda$ in place of $\lambda(2Cq)^\beta$, the failure term $M/\Lambda^{2q}$ for the moment budget $M$, and, in the last one, $\mu(A^c)$ for the complement of the event on which the energy and the moments are controlled. With $\Lambda=\lambda(2Cq)^\beta$ and $M=(2Cq)^{2\beta q}$ the failure term is $\lambda^{-2q}$ (`logarithmic_moment_holder_failure_identity`). The earlier square-root form (`logarithmic_integral_concentration`, with variants on an event and with restricted moments) remains, and the formal proofs for the coefficient distributions use it. In both forms, as in the paper, the occupation hypotheses enter through bounds on the mean and the variance of the angular occupation, and for each coefficient distribution the formal proof verifies these hypotheses.
- The component bounds of the mesh estimate of Theorem B.4 are formal, and the formalization assembles them for each coefficient distribution.
- The formal radial laws use four secant bounds of fixed width for the unweighted profile, followed by a countable squeezing argument, in place of the general Lemma B.3.

**Gaussian comparisons.** Lemma 4.4, the comparison of Gaussian laws through relative entropy, is kept in the paper but no longer used there, since the proof of Lemma 4.5 compares the law of a separated pair of jets with the product of its marginal laws through the interpolation bound (14). The formal proofs compare Gaussian laws through relative entropy and Pinsker's inequality throughout (`abs_measureReal_sub_le_of_klDiv_le` and `gaussian_measureReal_sub_le_of_quadratic_error`), including this paired comparison (`gaussian_measureReal_sub_le_eight`), with the constant $\sqrt{d/2}$ times the relative covariance error.

**Exponents of the intermediate estimates.**
- In the paper, Theorem 3.1 has the error $N^{-5/32}(\log N)^7$ and the failure probability $C(K)N^{-3/16}+N^{-12}+C(K)N^{-3/16}(\log N)^{-12}$, from the Hölder form of Theorem B.1, and Lemma 4.5 bounds the number of annular roots with a small derivative by $C(K)NL^{-4}\log N=C(K)N^{15/16}\log N$, with failure probability $N^{-3}+N^{-10}+C(K)N^{-5/16}(\log N)^2$, from Chebyshev's inequality at $t=NL^{-4}$.
- The formalization keeps the exponents of the earlier square-root route: the logarithmic tolerance $N^{-1/32}(\log N)^7$ (`logarithmicTolerance`), with failure terms of orders $N^{-3/8}$, $N^{-12}$ and $N^{-7/16}(\log N)^{-12}$, whose sum is at most $(2H+1)N^{-3/8}$ (`logarithmic_failure_le`), and the small-derivative threshold $N^{31/32}$, with failure probability $N^{-3}+N^{-10}+CN^{-3/8}(\log N)^4$ (`eventually_annular_small_derivative_probability`). At the growing width of Theorem 1.3, the tolerance and the count threshold are those of the section on the constant 128.
- Both sets of exponents make the exceptional probabilities summable along the degrees $N=j^8$ and give the same main theorems. Proposition 8.1 is stated for the earlier powers, as is its formal counterpart, and the range $8/3<q<16$ of `admissible_fixed_sparse_degree_scales` is that of the proposition.

## Modules

The figure below shows the modules of the formalization. Each lower box names a result of the paper and the module of its declaration, and `Erdos522.All` imports every one of them for the kernel replay.

<p align="center"><img src="../figures/lean-map.png" width="640" alt="Modules of the Lean formalization"></p>

## References

- [Bentkus2005] V. Bentkus, A Lyapunov-type bound in $\mathbb R^d$, *Theory of Probability and Its Applications* 49(2):311–323, 2005.
- [NNS2013] F. Nazarov, A. Nishry and M. Sodin, Log-integrability of Rademacher Fourier series, with applications to random analytic functions, *Algebra i Analiz* 25(3):147–184, 2013.
- [Raic2019] M. Raič, A multivariate Berry–Esseen theorem with explicit constants, *Bernoulli* 25(4A):2824–2853, 2019.
- [RudelsonVershynin2013] M. Rudelson and R. Vershynin, Hanson–Wright inequality and sub-gaussian concentration, *Electronic Communications in Probability* 18(82):1–9, 2013.

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522
import Lean.Util.CollectAxioms

/-!
# Public theorem statements and logical dependencies

The declarations below give the coefficient-uniform logarithmic estimate,
the unweighted radial laws, their quantitative refinements, and the weighted
variance and sublevel-crossing results. Their complete types retain each
model's hypotheses and the multiplicity-counted closed-disk conventions.
-/

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    -- Coefficient-uniform logarithmic moments.
    `Erdos522.harmonic_l2_restriction,
    `Erdos522.LogMoments.uniform_logarithmic_moments,
    `Erdos522.LogMoments.fourierPolynomial_ae_ne_zero,
    -- The Rademacher strong law and simultaneous radial profile.
    `Erdos522.erdos_522,
    `Erdos522.erdos_522_of_independent_coins,
    `Erdos522.radial_profile,
    `Erdos522.radial_profile_compact_uniform_prefixes,
    `Erdos522.iid_rademacher_radial_profile,
    -- Real Gaussian coefficients.
    `Erdos522.gaussian_zero_distribution,
    `Erdos522.gaussian_radial_profile,
    `Erdos522.gaussian_radial_profile_compact_uniform_prefixes,
    `Erdos522.iid_gaussian_radial_profile,
    -- Circular complex Gaussian coefficients.
    `Erdos522.circularGaussian_zero_distribution,
    `Erdos522.circularGaussian_radial_profile,
    `Erdos522.circularGaussian_radial_profile_compact_uniform_prefixes,
    `Erdos522.iid_circularGaussian_radial_profile,
    -- Steinhaus coefficients.
    `Erdos522.steinhaus_zero_distribution,
    `Erdos522.steinhaus_radial_profile,
    `Erdos522.steinhaus_radial_profile_compact_uniform_prefixes,
    `Erdos522.iid_steinhaus_radial_profile,
    -- Bounded centrally symmetric laws, including an atom at zero.
    `Erdos522.bounded_symmetric_zero_distribution_of_nontrivial,
    `Erdos522.bounded_symmetric_radial_profile_of_nontrivial,
    `Erdos522.bounded_symmetric_radial_profile_compact_uniform_of_nontrivial,
    `Erdos522.iid_bounded_symmetric_zero_distribution,
    `Erdos522.iid_bounded_symmetric_radial_profile,
    -- The logarithmic almost-sure rate and admissible degree schedules.
    `Erdos522.ae_rademacher_logarithmic_root_rate,
    `Erdos522.ae_rademacher_logarithmic_root_rate_eventually,
    `Erdos522.ae_radial_profile_via_real_power_degrees,
    `Erdos522.ae_radial_profile_via_fixed_degree_scales,
    `Erdos522.admissible_sparse_degree_scales,
    `Erdos522.admissible_fixed_sparse_degree_scales,
    `Erdos522.two_lt_of_occupation_summability,
    -- Power-weighted variance profiles, logarithmic moments, and exact energy.
    `Erdos522.log_weightedRadialSigma_profile_compact_uniform,
    `Erdos522.deriv_weightedLogVarianceProfile,
    `Erdos522.deriv_weightedLogVarianceProfile_zero,
    `Erdos522.integrable_weighted_logarithmic_moment,
    `Erdos522.integral_weighted_logarithmic_moment_le,
    `Erdos522.integral_weighted_normalized_energy,
    `Erdos522.log_weightedRadialSigmaWithConstant_profile_compact_uniform,
    `Erdos522.weighted_logarithmic_moments_with_constant,
    `Erdos522.integral_weighted_normalized_energy_with_constant,
    -- Summable control of sublevel components meeting nearby circles.
    `Erdos522.exists_summable_sublevel_crossing_envelope,
    `Erdos522.fixed_level_nearby_circle_sublevel_counts_summable,
    `Erdos522.nearby_circle_sublevel_counts_summable,
    `Erdos522.ae_nearby_circle_sublevel_counts_tendsto_zero]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "Missing public theorem {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Public endpoint {name} is not a theorem"
    logInfo m!"{name} : {info.type}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    logInfo m!"Logical dependencies of {name}: {axioms}"
  logInfo m!"Checked {names.size} public theorems: only propext, Classical.choice, Quot.sound."

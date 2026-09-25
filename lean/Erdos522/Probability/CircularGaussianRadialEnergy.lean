/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianRepresentation
import Erdos522.Probability.GaussianRadialEnergy
import Erdos522.Probability.SymmetricLogarithmicConcentration

/-!
# Angular energy of circular Gaussian polynomials

Parseval splits the complex angular energy into the average of two independent
real Gaussian energies. Their exponential upper tails therefore give a uniform
energy event for normalized logarithmic concentration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Erdos522

/-- A circular coordinate has half the sum of the squared real coordinates. -/
theorem norm_sq_circularGaussianCoordinateEquiv (p : ℝ × ℝ) :
    ‖circularGaussianCoordinateEquiv p‖ ^ 2 = (p.1 ^ 2 + p.2 ^ 2) / 2 := by
  rw [circularGaussianCoordinateEquiv_apply, norm_div, div_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- The weighted complex energy is the average of its real-coordinate energies. -/
theorem circularGaussian_weighted_energy_split {n : ℕ} (w : Fin n → ℝ)
    (g : (Fin n → ℝ) × (Fin n → ℝ)) :
    (∑ k, w k * ‖circularGaussianCoefficientVectorEquiv n g k‖ ^ 2) =
      (gaussianWeightedEnergy w g.1 + gaussianWeightedEnergy w g.2) / 2 := by
  change (∑ k, w k * ‖circularGaussianCoordinateEquiv (g.1 k, g.2 k)‖ ^ 2) = _
  simp_rw [norm_sq_circularGaussianCoordinateEquiv]
  simp only [gaussianWeightedEnergy, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Parseval expresses circular Gaussian angular energy in real Gaussian coordinates. -/
theorem integral_normalizedCircularGaussian_energy (N : ℕ) (r : ℝ)
    (g : (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
    (∫ θ, normalizedCoefficientValueModulus N r
      (θ, circularGaussianCoefficientVectorEquiv (N + 1) g) ^ 2 ∂radianIntervalMeasure) =
      (gaussianWeightedEnergy (radialEnergyWeight N r) g.1 +
        gaussianWeightedEnergy (radialEnergyWeight N r) g.2) / 2 := by
  rw [integral_normalizedCoefficientValueModulus_sq]
  simp only [norm_mul, mul_pow, norm_sq_normalizedRadialCoefficients]
  exact circularGaussian_weighted_energy_split _ g

/-- The complex normalized angular energy exceeds two with at most twice the
real Gaussian exponential exceptional probability. -/
theorem circularGaussian_radial_energy_gt_two_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) {a | 2 <
      ∫ θ, normalizedCoefficientValueModulus N r (θ, a) ^ 2 ∂radianIntervalMeasure} ≤
      ENNReal.ofReal (2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K)))) := by
  let E : Set (Fin (N + 1) → ℝ) :=
    {g | 2 < gaussianWeightedEnergy (radialEnergyWeight N r) g}
  have ht := circularGaussian_coefficient_event_le (N + 1)
    {a | 2 < ∫ θ, normalizedCoefficientValueModulus N r (θ, a) ^ 2 ∂radianIntervalMeasure}
    E E (by
      intro g hg
      change 2 < ∫ θ, normalizedCoefficientValueModulus N r
        (θ, circularGaussianCoefficientVectorEquiv (N + 1) g) ^ 2 ∂radianIntervalMeasure at hg
      rw [integral_normalizedCircularGaussian_energy] at hg
      change 2 < gaussianWeightedEnergy (radialEnergyWeight N r) g.1 ∨
        2 < gaussianWeightedEnergy (radialEnergyWeight N r) g.2
      by_contra h
      push Not at h
      linarith)
  have hp := gaussian_radial_energy_gt_two_le N hN K r hK hNK hrl hru
  simp only [integral_normalizedGaussianPolynomial_energy] at hp
  have hp' : (gaussianCoefficientMeasure (N + 1)).real E ≤
      Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    simpa only [E, measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hb : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {a | 2 < ∫ θ, normalizedCoefficientValueModulus N r (θ, a) ^ 2 ∂radianIntervalMeasure} ≤
      2 * Real.exp (-3 * (N : ℝ) / (32 * Real.exp (6 * K))) :=
    ht.trans ((add_le_add hp' hp').trans_eq (by ring))
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hb

end Erdos522

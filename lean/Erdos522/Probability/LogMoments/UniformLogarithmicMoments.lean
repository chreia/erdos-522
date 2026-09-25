/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HarmonicRestriction

/-!
# Uniform logarithmic moments of Rademacher Fourier sums

Harmonic restriction and the Fourier spreading argument yield logarithmic
moments uniformly over all normalized finite complex coefficient vectors.
The normalization uses Haar probability measure on the circle of period one
and the uniform product law of the signs.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The absolute constant in the finite Rademacher logarithmic-moment bound. -/
def rademacherLogarithmicConstant : ℝ :=
  fourierLogarithmicConstant harmonicRestrictionConstant

theorem rademacherLogarithmicConstant_pos : 0 < rademacherLogarithmicConstant :=
  fourierLogarithmicConstant_pos one_le_harmonicRestrictionConstant

/-- Every positive-measure set captures Fourier energy with a sixth-power
logarithmic loss, uniformly in the finite coefficient vector. -/
theorem restricted_fourier_energy_lower_bound {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) :
    1 ≤ Real.exp (fourierEnergyExponent harmonicRestrictionConstant *
      Real.log (2 / (fourierMeasure N).real E) ^ 6) *
        ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N :=
  restricted_fourier_energy_lower_bound_of_harmonic_restriction
    one_le_harmonicRestrictionConstant harmonic_l2_restriction a ha E hE hpos

/-- The negative logarithm has a uniformly integrable stretched exponential. -/
theorem negative_log_stretched_exponential {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1) :
    Integrable (fun z => Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (randomFourier a z) /
        fourierEnergyExponent harmonicRestrictionConstant) ^ ((6 : ℝ)⁻¹)))
      (fourierMeasure N) ∧
    (∫ z, Real.exp ((1 / 2 : ℝ) *
      (negativeLogNorm (randomFourier a z) /
        fourierEnergyExponent harmonicRestrictionConstant) ^ ((6 : ℝ)⁻¹))
      ∂fourierMeasure N) ≤ 3 :=
  negative_log_stretched_exponential_of_harmonic_restriction
    one_le_harmonicRestrictionConstant harmonic_l2_restriction a ha

/-- All real moments of the negative logarithm obey a sixth-power scale. -/
theorem negative_log_moments {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => negativeLogNorm (randomFourier a z) ^ p) (fourierMeasure N) ∧
      (∫ z, negativeLogNorm (randomFourier a z) ^ p ∂fourierMeasure N) ≤
        (36 * fourierEnergyExponent harmonicRestrictionConstant * p) ^ (6 * p) :=
  negative_log_moments_of_harmonic_restriction
    one_le_harmonicRestrictionConstant harmonic_l2_restriction a ha hp

/-- Coefficient-uniform absolute logarithmic moments for every real `p≥1`. -/
theorem uniform_logarithmic_moments {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1)
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => |Real.log ‖randomFourier a z‖| ^ p) (fourierMeasure N) ∧
      (∫ z, |Real.log ‖randomFourier a z‖| ^ p ∂fourierMeasure N) ≤
        (rademacherLogarithmicConstant * p) ^ (6 * p) :=
  uniform_logarithmic_moments_of_harmonic_restriction
    one_le_harmonicRestrictionConstant harmonic_l2_restriction a ha hp

end Erdos522.LogMoments

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CoefficientNormalization
import Erdos522.Probability.SymmetricRadialProfile

/-!
# Radial laws without variance normalization

Multiplication by the reciprocal standard deviation leaves every root unchanged.
Consequently every bounded centrally symmetric coefficient law with positive
probability of a nonzero coefficient has the same almost-sure Kac radial profile.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- A nontrivial bounded coefficient law admits bounded unit-variance normalization. -/
theorem exists_bounded_unit_variance_scaling (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {B : ℝ} (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hzero : μ {0} < 1) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ D : ℝ, 1 ≤ D ∧
      (∀ᵐ z ∂scaledCoefficientMeasure μ a, ‖z‖ ≤ D) ∧
      (∫ z, ‖z‖ ^ 2 ∂scaledCoefficientMeasure μ a) = 1 := by
  let v := ∫ z, ‖z‖ ^ 2 ∂μ
  have hv : 0 < v := integral_norm_sq_pos_of_bounded μ hbound hzero
  let a : ℂ := (Real.sqrt v : ℂ)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne')
  refine ⟨a, ha, max 1 (‖a‖ * B), le_max_left _ _, ?_, ?_⟩
  · filter_upwards [ae_norm_scaledCoefficientMeasure_le μ a hbound] with z hz
    exact hz.trans (le_max_right _ _)
  · exact integral_norm_sq_normalizedCoefficientMeasure μ hv rfl

/-- The scaled radial fraction is invariant under common nonzero coefficient scaling. -/
theorem coefficientScaledRadialFraction_scale {a : ℂ} (ha : a ≠ 0) (ω : ℕ → ℂ) :
    coefficientScaledRadialFraction (fun k => a * ω k) =
      coefficientScaledRadialFraction ω := by
  funext N x
  simp only [coefficientScaledRadialFraction, coefficientRadialFraction,
    coefficientPrefix_polynomial, closedZeroCount_prefix_mul_coefficients ha]

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    {B : ℝ} (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hzero : μ {0} < 1)

include hbound hzero

/-- Every bounded nontrivial centrally symmetric law has the full radial profile
on one probability-one event, without a variance normalization hypothesis. -/
theorem bounded_symmetric_radial_profile_of_nontrivial :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ x : ℝ,
      Tendsto (fun N : ℕ => coefficientScaledRadialFraction ω N x)
        atTop (𝓝 (kacRadialProfile x)) := by
  obtain ⟨a, ha, D, hD, hnorm, hsecond⟩ :=
    exists_bounded_unit_variance_scaling μ hbound hzero
  apply ae_coefficientSequence_of_scale μ a _
    (fun ω => by simp only [coefficientScaledRadialFraction_scale ha])
  exact bounded_symmetric_radial_profile (scaledCoefficientMeasure μ a) hD hnorm hsecond

/-- The full radial profile is almost surely uniform on every compact real set
for any bounded nontrivial centrally symmetric coefficient law. -/
theorem bounded_symmetric_radial_profile_compact_uniform_of_nontrivial :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s := by
  obtain ⟨a, ha, D, hD, hnorm, hsecond⟩ :=
    exists_bounded_unit_variance_scaling μ hbound hzero
  apply ae_coefficientSequence_of_scale μ a _
    (fun ω => by simp only [closedZeroCount_prefix_mul_coefficients ha])
  exact bounded_symmetric_radial_profile_compact_uniform_prefixes
    (scaledCoefficientMeasure μ a) hD hnorm hsecond

/-- The closed-unit-disk strong law for bounded centrally symmetric coefficients.
The law may have an atom at zero, provided it is not concentrated there. -/
theorem bounded_symmetric_zero_distribution_of_nontrivial :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ,
      Tendsto (fun N : ℕ =>
        (closedZeroCount (polynomialPrefix ω (fun _ => 1) N) 1 : ℝ) / N)
        atTop (𝓝 (1 / 2 : ℝ)) := by
  filter_upwards [bounded_symmetric_radial_profile_of_nontrivial μ hbound hzero] with ω hω
  simpa only [coefficientScaledRadialFraction, coefficientRadialFraction,
    zero_div, add_zero, kacRadialProfile_zero, coefficientPrefix_polynomial] using hω 0

end Erdos522

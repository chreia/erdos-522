/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.ScalarNormalization
import Erdos522.Probability.CoefficientSequence
import Mathlib.MeasureTheory.Group.Integral

/-!
# Normalization of coefficient laws

A nonzero common scalar preserves all zeros of every prefix. Scaling the
coefficient law transports the entire infinite product sequence and rescales
the second moment, allowing unit-variance theorems to apply to arbitrary
positive finite variance.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Erdos522

/-- The law obtained by multiplying a complex coefficient by a fixed scalar. -/
def scaledCoefficientMeasure (μ : Measure ℂ) (a : ℂ) : Measure ℂ :=
  μ.map (fun z => a * z)

instance (μ : Measure ℂ) [IsProbabilityMeasure μ] (a : ℂ) :
    IsProbabilityMeasure (scaledCoefficientMeasure μ a) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- Central symmetry is preserved under multiplication by any complex scalar. -/
instance (μ : Measure ℂ) [μ.IsNegInvariant] (a : ℂ) :
    (scaledCoefficientMeasure μ a).IsNegInvariant where
  neg_eq_self := by
    change Measure.map (fun z : ℂ => -z) (μ.map (fun z => a * z)) = μ.map (fun z => a * z)
    rw [Measure.map_map measurable_neg (by fun_prop)]
    have he : (fun z : ℂ => -z) ∘ (fun z => a * z) =
        (fun z => a * z) ∘ (fun z => -z) := by ext z; simp
    rw [he, ← Measure.map_map (by fun_prop) measurable_neg, Measure.map_neg_eq_self]

/-- Scaling every coordinate has the infinite product of the scaled coefficient law. -/
theorem map_coefficientSequence_scale (μ : Measure ℂ) [IsProbabilityMeasure μ] (a : ℂ) :
    (coefficientSequenceMeasure μ).map (fun ω : ℕ → ℂ => fun k => a * ω k) =
      coefficientSequenceMeasure (scaledCoefficientMeasure μ a) := by
  unfold coefficientSequenceMeasure scaledCoefficientMeasure
  exact Measure.infinitePi_map_pi _ (fun _ => by fun_prop)

theorem measurePreserving_coefficientSequence_scale (μ : Measure ℂ) [IsProbabilityMeasure μ] (a : ℂ) :
    MeasurePreserving (fun ω : ℕ → ℂ => fun k => a * ω k)
      (coefficientSequenceMeasure μ) (coefficientSequenceMeasure (scaledCoefficientMeasure μ a)) :=
  ⟨by fun_prop, map_coefficientSequence_scale μ a⟩

/-- The second moment scales by the squared scalar modulus. -/
theorem integral_norm_sq_scaledCoefficientMeasure (μ : Measure ℂ) (a : ℂ) :
    (∫ z, ‖z‖ ^ 2 ∂scaledCoefficientMeasure μ a) = ‖a‖ ^ 2 * ∫ z, ‖z‖ ^ 2 ∂μ := by
  rw [scaledCoefficientMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_mul, mul_pow, integral_const_mul]

/-- A coefficient bound scales by the scalar modulus. -/
theorem ae_norm_scaledCoefficientMeasure_le (μ : Measure ℂ) (a : ℂ) {B : ℝ}
    (hB : ∀ᵐ z ∂μ, ‖z‖ ≤ B) :
    ∀ᵐ z ∂scaledCoefficientMeasure μ a, ‖z‖ ≤ ‖a‖ * B := by
  rw [scaledCoefficientMeasure, ae_map_iff (by fun_prop)
    (measurableSet_le (by fun_prop) measurable_const)]
  filter_upwards [hB] with z hz
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg a)

/-- Positive second moment admits exact unit-variance normalization. -/
theorem integral_norm_sq_normalizedCoefficientMeasure (μ : Measure ℂ) {v : ℝ}
    (hv : 0 < v) (hvar : (∫ z, ‖z‖ ^ 2 ∂μ) = v) :
    (∫ z, ‖z‖ ^ 2 ∂scaledCoefficientMeasure μ ((Real.sqrt v : ℂ)⁻¹)) = 1 := by
  rw [integral_norm_sq_scaledCoefficientMeasure, hvar, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg v), inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

/-- A bounded law not concentrated at zero has positive second moment. -/
theorem integral_norm_sq_pos_of_bounded (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {B : ℝ} (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hzero : μ {0} < 1) :
    0 < ∫ z, ‖z‖ ^ 2 ∂μ := by
  have h2 : MemLp (fun z : ℂ => z) 2 μ := MemLp.of_bound (by fun_prop) B hbound
  have hnonneg : 0 ≤ ∫ z, ‖z‖ ^ 2 ∂μ := integral_nonneg (fun z => sq_nonneg ‖z‖)
  by_contra! h
  have he := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖z‖) h2.norm.integrable_sq).mp
    (le_antisymm h hnonneg)
  have hz : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ) := by
    filter_upwards [he] with z hz
    simpa using hz
  have hone : μ {0} = 1 := by
    simpa using (ae_iff_measure_eq (by measurability)).mp hz
  exact (ne_of_lt hzero) hone

/-- Almost-sure statements invariant under common scaling transfer
from the normalized infinite coefficient law to the original sequence. -/
theorem ae_coefficientSequence_of_scale (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (a : ℂ) (P : (ℕ → ℂ) → Prop)
    (hscale : ∀ ω, P (fun k => a * ω k) ↔ P ω)
    (hP : ∀ᵐ ω ∂coefficientSequenceMeasure (scaledCoefficientMeasure μ a), P ω) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, P ω := by
  have h := (measurePreserving_coefficientSequence_scale μ a).quasiMeasurePreserving.ae hP
  filter_upwards [h] with ω hω
  exact (hscale ω).mp hω

end Erdos522

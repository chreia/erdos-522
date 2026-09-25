/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.GeometricMean
import Erdos522.Probability.ExponentialTailIntegral

/-!
# Geometric quotient bounds from weak distribution estimates

A weak `1/u` bound for a modulus ratio controls the integral of its positive
logarithm. Clipping at the logarithm of inverse set mass yields one factor of
inverse mass in the geometric mean, so repeated frequency elimination keeps
the original measurable set.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Erdos522

/-- The excess of a logarithm above a fixed height. -/
def positiveLogarithmicTail {Ω : Type*} (R : Ω → ℝ) (T : ℝ) (x : Ω) : ℝ :=
  max (Real.log (R x) - T) 0

/-- A weak bound becomes an exponential bound for the logarithmic excess. -/
theorem positiveLogarithmicTail_distribution_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ℝ) (hR : ∀ x, 0 ≤ R x) {A T : ℝ}
    (hT : 0 ≤ T)
    (hweak : ∀ u : ℝ, 0 < u → μ {x | u ≤ R x} ≤ ENNReal.ofReal (A / u))
    {s : ℝ} (hs : 0 < s) :
    μ {x | s ≤ positiveLogarithmicTail R T x} ≤
      ENNReal.ofReal (A * Real.exp (-T) * Real.exp (-s)) := by
  have hsub : {x | s ≤ positiveLogarithmicTail R T x} ⊆
      {x | Real.exp (T + s) ≤ R x} := by
    intro x hx
    change s ≤ max (Real.log (R x) - T) 0 at hx
    have hlog : T + s ≤ Real.log (R x) := by
      rcases le_max_iff.mp hx with h | h
      · linarith
      · linarith
    have hpos : 0 < R x := by
      by_contra h
      have hz : R x = 0 := le_antisymm (le_of_not_gt h) (hR x)
      rw [hz, Real.log_zero] at hlog
      linarith
    exact (Real.le_log_iff_exp_le hpos).mp hlog
  refine (measure_mono hsub).trans ((hweak _ (Real.exp_pos _)).trans_eq ?_)
  congr 1
  rw [Real.exp_add, div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv,
    ← Real.exp_neg, ← Real.exp_neg]

/-- The logarithmic excess has integral at most `A exp(-T)`. -/
theorem integrable_positiveLogarithmicTail_and_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ℝ)
    (hRm : Measurable R) (hR : ∀ x, 0 ≤ R x) {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hweak : ∀ u : ℝ, 0 < u → μ {x | u ≤ R x} ≤ ENNReal.ofReal (A / u)) :
    Integrable (positiveLogarithmicTail R T) μ ∧
      (∫ x, positiveLogarithmicTail R T x ∂μ) ≤ A * Real.exp (-T) := by
  have hm : Measurable (positiveLogarithmicTail R T) :=
    (hRm.log.sub measurable_const).max measurable_const
  simpa only [one_mul, div_one] using integrable_and_integral_le_of_exponential_tail μ
    (positiveLogarithmicTail R T) hm (fun _ => le_max_right _ _) (A * Real.exp (-T)) 1
    (mul_nonneg hA (Real.exp_pos _).le) (by norm_num)
    (fun s hs => by simpa using positiveLogarithmicTail_distribution_le μ R hR hT hweak hs)

/-- Integrating a weak bound over a finite measure costs its mass times
`1 + log(A/mass)`. -/
theorem integrable_positive_log_and_integral_le_of_weak_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → ℝ) (hRm : Measurable R) (hR : ∀ x, 0 ≤ R x)
    (hμ : 0 < μ.real univ) {A : ℝ} (hA : μ.real univ ≤ A)
    (hweak : ∀ u : ℝ, 0 < u → μ {x | u ≤ R x} ≤ ENNReal.ofReal (A / u)) :
    Integrable (fun x => max (Real.log (R x)) 0) μ ∧
      (∫ x, max (Real.log (R x)) 0 ∂μ) ≤
        μ.real univ * (1 + Real.log (A / μ.real univ)) := by
  let T := Real.log (A / μ.real univ)
  have hApos : 0 < A := hμ.trans_le hA
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div hμ).mpr hA)
  have heq : A * Real.exp (-T) = μ.real univ := by
    dsimp [T]
    rw [Real.exp_neg, Real.exp_log (div_pos hApos hμ)]
    field_simp
  obtain ⟨htail, htint⟩ := integrable_positiveLogarithmicTail_and_integral_le
    μ R hRm hR hApos.le hT hweak
  rw [heq] at htint
  have hbound (x : Ω) : max (Real.log (R x)) 0 ≤ T + positiveLogarithmicTail R T x := by
    apply max_le
    · have := le_max_left (Real.log (R x) - T) 0
      dsimp [positiveLogarithmicTail]
      linarith
    · exact add_nonneg hT (le_max_right _ _)
  have hdom := (integrable_const T).add htail
  have hint : Integrable (fun x => max (Real.log (R x)) 0) μ :=
    hdom.mono_nonneg (hRm.log.max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun _ => le_max_right _ _) (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x, T + positiveLogarithmicTail R T x ∂μ := integral_mono hint hdom hbound
    _ = μ.real univ * T + ∫ x, positiveLogarithmicTail R T x ∂μ := by
      rw [integral_add (integrable_const T) htail, integral_const, smul_eq_mul]
    _ ≤ μ.real univ * T + μ.real univ := add_le_add (le_refl _) htint
    _ = _ := by dsimp [T]; ring

/-- A weak modulus-ratio estimate transfers geometric means with the exact
factor `exp(1) A / mass`. Both logarithmic moduli are integrable. -/
theorem geometricMean_quotient_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hflog : Integrable (fun x => Real.log ‖f x‖) μ)
    (hglog : Integrable (fun x => Real.log ‖g x‖) μ)
    (hfzero : ∀ᵐ x ∂μ, f x ≠ 0) (hgzero : ∀ᵐ x ∂μ, g x ≠ 0)
    (hμ : 0 < μ.real univ) {A : ℝ} (hA : μ.real univ ≤ A)
    (hweak : ∀ u : ℝ, 0 < u →
      μ {x | u ≤ ‖g x‖ / ‖f x‖} ≤ ENNReal.ofReal (A / u)) :
    geometricMean μ g ≤ (Real.exp 1 * A / μ.real univ) * geometricMean μ f := by
  let R := fun x => ‖g x‖ / ‖f x‖
  obtain ⟨hpositive, hint⟩ := integrable_positive_log_and_integral_le_of_weak_bound
    μ R (hg.norm.div hf.norm) (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _)) hμ hA hweak
  have hlog : ∀ᵐ x ∂μ, Real.log ‖g x‖ ≤ Real.log ‖f x‖ + max (Real.log (R x)) 0 := by
    filter_upwards [hfzero, hgzero] with x hfx hgx
    have h := le_max_left (Real.log (R x)) 0
    dsimp [R] at h
    rw [Real.log_div (norm_ne_zero_iff.mpr hgx) (norm_ne_zero_iff.mpr hfx)] at h
    dsimp [R]
    rw [Real.log_div (norm_ne_zero_iff.mpr hgx) (norm_ne_zero_iff.mpr hfx)]
    linarith
  have havg : (⨍ x, max (Real.log (R x)) 0 ∂μ) ≤ 1 + Real.log (A / μ.real univ) := by
    rw [average_eq, smul_eq_mul]
    calc
      _ ≤ (μ.real univ)⁻¹ * (μ.real univ * (1 + Real.log (A / μ.real univ))) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hμ.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul]
  have hsum := average_mono_of_integrable hglog (hflog.add hpositive) hlog
  rw [average_add hflog hpositive] at hsum
  have hcomparison : (⨍ x, Real.log ‖g x‖ ∂μ) ≤
      (1 + Real.log (A / μ.real univ)) + ⨍ x, Real.log ‖f x‖ ∂μ := by linarith
  have h := geometricMean_le_exp_mul_of_average_bound μ f g _ hcomparison
  rw [Real.exp_add, Real.exp_log (div_pos (hμ.trans_le hA) hμ)] at h
  simpa only [mul_div_assoc] using h

end Erdos522

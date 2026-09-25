/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.AmplitudeLogarithmicMoments

/-!
# Logarithmic moments conditional on independent amplitudes

On an amplitude event where the Fourier coefficient energy lies in
`[1/2,B²]`, integrating the conditional sign estimate gives the same
sixth-power logarithmic moment bound for the product probability law.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Fourier evaluation is jointly measurable in measurable coefficients,
the finite sign vector, and the circle parameter. -/
theorem measurable_randomFourier_with_coefficients {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (a : Ω → Fin (N + 1) → ℂ) (ha : ∀ k, Measurable (fun ω => a ω k)) :
    Measurable (fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) => randomFourier (a q.1) q.2) := by
  simp only [randomFourier, fourierPolynomial_eq_sum]
  have hs (k : Fin (N + 1)) : Measurable
      (fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) => sign (q.2.1 k)) :=
    (measurable_of_finite (fun ω : SignVector N => sign (ω k))).comp
      (measurable_fst.comp measurable_snd)
  have hc (k : Fin (N + 1)) : Measurable
      (fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) => a q.1 k) :=
    (ha k).comp measurable_fst
  fun_prop

/-- Integrating over independent amplitudes preserves the conditional
logarithmic moment bound on the amplitude event, with its exact mass. -/
theorem conditional_logarithmic_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    (a : Ω → Fin (N + 1) → ℂ) (ha : ∀ k, Measurable (fun ω => a ω k))
    (E : Set Ω) (hE : MeasurableSet E) {B p : ℝ}
    (hlo : ∀ ω ∈ E, 1 / 2 ≤ ∑ k, ‖a ω k‖ ^ 2)
    (hhi : ∀ ω ∈ E, ∑ k, ‖a ω k‖ ^ 2 ≤ B ^ 2) (hp : 1 ≤ p) :
    Integrable (fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) =>
      |Real.log ‖randomFourier (a q.1) q.2‖| ^ p) ((μ.restrict E).prod (fourierMeasure N)) ∧
    (∫ q, |Real.log ‖randomFourier (a q.1) q.2‖| ^ p
      ∂((μ.restrict E).prod (fourierMeasure N))) ≤
        μ.real E * (amplitudeLogarithmicConstant B * p) ^ (6 * p) := by
  let f := fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) =>
    |Real.log ‖randomFourier (a q.1) q.2‖| ^ p
  have hf : Measurable f := by
    simpa only [f, Real.norm_eq_abs] using
      (measurable_randomFourier_with_coefficients a ha).norm.log.norm.pow_const p
  have hnon (q) : 0 ≤ f q := Real.rpow_nonneg (abs_nonneg _) _
  have hconditional : ∀ᵐ ω ∂μ.restrict E,
      Integrable (fun z => f (ω, z)) (fourierMeasure N) ∧
        (∫ z, f (ω, z) ∂fourierMeasure N) ≤
          (amplitudeLogarithmicConstant B * p) ^ (6 * p) := by
    filter_upwards [ae_restrict_mem hE] with ω hω
    exact uniform_logarithmic_moments_of_bounded_energy (a ω) (hlo ω hω) (hhi ω hω) hp
  have hinner : Integrable (fun ω => ∫ z, ‖f (ω, z)‖ ∂fourierMeasure N) (μ.restrict E) := by
    apply (integrable_const ((amplitudeLogarithmicConstant B * p) ^ (6 * p))).mono'
      hf.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [hconditional] with ω hω
    have heq : (∫ z, ‖f (ω, z)‖ ∂fourierMeasure N) = ∫ z, f (ω, z) ∂fourierMeasure N := by
      congr 1
      funext z
      exact Real.norm_of_nonneg (hnon _)
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => hnon (ω, z)))]
    exact hω.2
  have hI : Integrable f ((μ.restrict E).prod (fourierMeasure N)) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr
      ⟨hconditional.mono (fun _ h => h.1), hinner⟩
  refine ⟨hI, ?_⟩
  change (∫ q, f q ∂((μ.restrict E).prod (fourierMeasure N))) ≤ _
  rw [integral_prod _ hI]
  have hbound := integral_mono_ae hI.integral_prod_left
    (integrable_const ((amplitudeLogarithmicConstant B * p) ^ (6 * p)))
    (hconditional.mono (fun _ h => h.2))
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] using hbound

/-- The event-restricted moment bound under the full independent product
law has an absolute constant depending only on the amplitude bound. -/
theorem event_restricted_logarithmic_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    (a : Ω → Fin (N + 1) → ℂ) (ha : ∀ k, Measurable (fun ω => a ω k))
    (E : Set Ω) (hE : MeasurableSet E) {B p : ℝ}
    (hlo : ∀ ω ∈ E, 1 / 2 ≤ ∑ k, ‖a ω k‖ ^ 2)
    (hhi : ∀ ω ∈ E, ∑ k, ‖a ω k‖ ^ 2 ≤ B ^ 2) (hp : 1 ≤ p) :
    IntegrableOn (fun q : Ω × (SignVector N × AddCircle (1 : ℝ)) =>
      |Real.log ‖randomFourier (a q.1) q.2‖| ^ p) (E ×ˢ univ) (μ.prod (fourierMeasure N)) ∧
    (∫ q in E ×ˢ univ, |Real.log ‖randomFourier (a q.1) q.2‖| ^ p
      ∂(μ.prod (fourierMeasure N))) ≤ (amplitudeLogarithmicConstant B * p) ^ (6 * p) := by
  obtain ⟨hI, hbound⟩ := conditional_logarithmic_moments μ a ha E hE hlo hhi hp
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
  refine ⟨hI, ?_⟩
  exact hbound.trans (mul_le_of_le_one_left (Real.rpow_nonneg (by
    have hC := rademacherLogarithmicConstant_pos
    have hH : 0 ≤ max ((1 / 2 : ℝ) * Real.log 2) (Real.log B) :=
      le_trans (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (le_max_left _ _)
    unfold amplitudeLogarithmicConstant
    positivity) _) measureReal_le_one)

end Erdos522.LogMoments

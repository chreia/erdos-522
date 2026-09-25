/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Variance of integrated random fields

Averaging a bounded random field cannot exceed its average variance.
This form of the covariance inequality applies directly to occupation integrals.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Erdos522

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- The square of an integral is bounded by the integral of the square under a probability law. -/
theorem sq_integral_le_integral_sq (ν : Measure Θ) [IsProbabilityMeasure ν]
    {f : Θ → ℝ} (hf : MemLp f 2 ν) :
    (∫ θ, f θ ∂ν) ^ 2 ≤ ∫ θ, f θ ^ 2 ∂ν := by
  have h := variance_nonneg f ν
  rw [variance_eq_sub hf] at h
  change 0 ≤ (∫ θ, f θ ^ 2 ∂ν) - (∫ θ, f θ ∂ν) ^ 2 at h
  linarith

/-- Integrating a bounded random field contracts its average variance. -/
theorem variance_integral_le_integral_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (F : Θ × Ω → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    variance (fun ω => ∫ θ, F (θ, ω) ∂ν) μ ≤
      ∫ θ, variance (fun ω => F (θ, ω)) μ ∂ν := by
  let m : Θ → ℝ := fun θ => ∫ ω, F (θ, ω) ∂μ
  let A : Ω → ℝ := fun ω => ∫ θ, F (θ, ω) ∂ν
  have hm : Measurable m := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hA : Measurable A := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hmn (θ : Θ) : ‖m θ‖ ≤ C := by
    simpa [m] using norm_integral_le_of_norm_le_const (μ := μ)
      (ae_of_all _ fun ω => hbound (θ, ω))
  have hAn (ω : Ω) : ‖A ω‖ ≤ C := by
    simpa [A] using norm_integral_le_of_norm_le_const (μ := ν)
      (ae_of_all _ fun θ => hbound (θ, ω))
  have hmLp : MemLp m 2 ν := MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ hmn)
  have hALp : MemLp A 2 μ := MemLp.of_bound hA.aestronglyMeasurable C (ae_of_all _ hAn)
  have hFLp : MemLp F 2 (ν.prod μ) :=
    MemLp.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)
  have hmean : (∫ ω, A ω ∂μ) = ∫ θ, m θ ∂ν :=
    (integral_integral_swap (f := fun θ ω => F (θ, ω)) (hFLp.integrable (by norm_num))).symm
  let Z : Θ × Ω → ℝ := fun p => F p - m p.1
  have hZ : Measurable Z := hF.sub (hm.comp measurable_fst)
  have hZn (p : Θ × Ω) : ‖Z p‖ ≤ 2 * C := by
    exact (norm_sub_le (F p) (m p.1)).trans (by linarith [hbound p, hmn p.1])
  have hZLp : MemLp Z 2 (ν.prod μ) :=
    MemLp.of_bound hZ.aestronglyMeasurable (2 * C) (ae_of_all _ hZn)
  have hcenter (ω : Ω) : A ω - (∫ ω, A ω ∂μ) = ∫ θ, Z (θ, ω) ∂ν := by
    have hsection : Integrable (fun θ => F (θ, ω)) ν :=
      (MemLp.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
        (ae_of_all _ fun θ => hbound (θ, ω)) : MemLp _ 1 ν).integrable (by norm_num)
    rw [integral_sub hsection (hmLp.integrable (by norm_num)), hmean]
  have hpoint (ω : Ω) : (A ω - (∫ ω, A ω ∂μ)) ^ 2 ≤ ∫ θ, Z (θ, ω) ^ 2 ∂ν := by
    rw [hcenter]
    exact sq_integral_le_integral_sq ν
      (MemLp.of_bound (hZ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable (2 * C)
        (ae_of_all _ fun θ => hZn (θ, ω)))
  change variance A μ ≤ _
  rw [variance_eq_integral hA.aemeasurable]
  calc
    _ ≤ ∫ ω, ∫ θ, Z (θ, ω) ^ 2 ∂ν ∂μ :=
      integral_mono (hALp.sub (memLp_const _)).integrable_sq
        hZLp.integrable_sq.integral_prod_right hpoint
    _ = ∫ θ, ∫ ω, Z (θ, ω) ^ 2 ∂μ ∂ν :=
      (integral_integral_swap (f := fun θ ω => Z (θ, ω) ^ 2) hZLp.integrable_sq).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with θ
      exact (variance_eq_integral
        ((hF.comp (measurable_const.prodMk measurable_id)).aemeasurable)).symm

/-- A uniform pointwise variance bound passes through a probability average. -/
theorem variance_integral_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (F : Θ × Ω → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C)
    (v : ℝ) (hvar : ∀ θ, variance (fun ω => F (θ, ω)) μ ≤ v) :
    variance (fun ω => ∫ θ, F (θ, ω) ∂ν) μ ≤ v := by
  have hm : Measurable (fun θ => ∫ ω, F (θ, ω) ∂μ) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have hVeq : (fun θ => variance (fun ω => F (θ, ω)) μ) =
      fun θ => ∫ ω, (F (θ, ω) - ∫ ω', F (θ, ω') ∂μ) ^ 2 ∂μ := by
    ext θ
    exact variance_eq_integral ((hF.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  have hV : Measurable (fun θ => variance (fun ω => F (θ, ω)) μ) := by
    rw [hVeq]
    exact ((hF.sub (hm.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hVint : Integrable (fun θ => variance (fun ω => F (θ, ω)) μ) ν :=
    (integrable_const v).mono' hV.aestronglyMeasurable
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs, abs_of_nonneg (variance_nonneg _ _)]; exact hvar θ)
  exact (variance_integral_le_integral_variance μ ν F hF C hbound).trans
    (by simpa using integral_mono hVint (integrable_const v) hvar)

/-- A finite parameter measure of mass `M` multiplies a uniform variance bound by `M²`. -/
theorem variance_integral_le_mass_sq_mul (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsFiniteMeasure ν] (F : Θ × Ω → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C)
    (v : ℝ) (hvar : ∀ θ, variance (fun ω => F (θ, ω)) μ ≤ v) :
    variance (fun ω => ∫ θ, F (θ, ω) ∂ν) μ ≤ ν.real Set.univ ^ 2 * v := by
  by_cases hν : ν = 0
  · subst ν
    simp only [integral_zero_measure, measureReal_zero_apply, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    exact le_of_eq (variance_zero μ)
  let : NeZero ν := ⟨hν⟩
  let ν' := (ν Set.univ)⁻¹ • ν
  have h := variance_integral_le μ ν' F hF C hbound v hvar
  simp only [ν', integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    variance_const_mul] at h
  have hM : 0 < ν.real Set.univ := measureReal_univ_pos
  change (ν.real Set.univ)⁻¹ ^ 2 * variance (fun ω => ∫ θ, F (θ, ω) ∂ν) μ ≤ v at h
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (ν.real Set.univ))
  field_simp at hh
  nlinarith

end Erdos522

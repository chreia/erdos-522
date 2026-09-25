/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ClippedLogarithm
import Erdos522.Probability.OccupationMoments
import Erdos522.Probability.IntegratedVariance

/-!
# Clipped logarithmic integrals from occupations

Layer cake expresses a clipped logarithm through its small-value levels.
Uniform occupation variance therefore gives the factor `4 T²` in the
variance of the clipped logarithmic integral.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Erdos522

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- The fraction of angular parameters below the exponential level. -/
def levelOccupation (ν : Measure Θ) (X : Θ × Ω → ℝ) (p : ℝ × Ω) : ℝ :=
  ν.real {θ | X (θ, p.2) ≤ Real.exp p.1}

/-- Small-value occupation is jointly measurable in the level and the random outcome. -/
theorem measurable_levelOccupation (ν : Measure Θ) [SFinite ν]
    (X : Θ × Ω → ℝ) (hX : Measurable X) : Measurable (levelOccupation ν X) := by
  let E : Set (Θ × (ℝ × Ω)) := {p | X (p.1, p.2.2) ≤ Real.exp p.2.1}
  have hE : MeasurableSet E := measurableSet_le (hX.comp (by fun_prop)) (by fun_prop)
  exact measurable_occupation ν hE

omit [MeasurableSpace Ω] in
/-- Every normalized occupation lies between zero and one. -/
theorem levelOccupation_mem_Icc (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ × Ω → ℝ) (p : ℝ × Ω) : levelOccupation ν X p ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The clipped logarithmic integral of a nonnegative random field. -/
def clippedLogarithmicIntegral (ν : Measure Θ) (X : Θ × Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  ∫ θ, clippedLogarithm T (X (θ, ω)) ∂ν

/-- The clipped logarithmic integral is measurable. -/
theorem measurable_clippedLogarithmicIntegral (ν : Measure Θ) [SFinite ν]
    (X : Θ × Ω → ℝ) (hX : Measurable X) (T : ℝ) :
    Measurable (clippedLogarithmicIntegral ν X T) :=
  ((measurable_clippedLogarithm T).comp hX).stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace Ω] in
/-- Clipping controls the logarithmic integral uniformly. -/
theorem norm_clippedLogarithmicIntegral_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ × Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    ‖clippedLogarithmicIntegral ν X T ω‖ ≤ T := by
  have hbound (θ : Θ) : ‖clippedLogarithm T (X (θ, ω))‖ ≤ T := by
    rw [Real.norm_eq_abs, abs_le]
    exact clippedLogarithm_mem_Icc T _ hT
  simpa [clippedLogarithmicIntegral] using norm_integral_le_of_norm_le_const (ae_of_all ν hbound)

/-- Integrating the scalar layer-cake formula yields the occupation identity. -/
theorem integral_clippedLogarithm_eq (ν : Measure Θ) [IsProbabilityMeasure ν]
    (f : Θ → ℝ) (hf : Measurable f) (hf0 : ∀ θ, 0 ≤ f θ)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ θ, clippedLogarithm T (f θ) ∂ν) =
      T - ∫ s in Icc (-T) T, ν.real {θ | f θ ≤ Real.exp s} := by
  let H : ℝ × Θ → ℝ := fun p => if f p.2 ≤ Real.exp p.1 then 1 else 0
  have hH : Measurable H := Measurable.ite
    (measurableSet_le (hf.comp measurable_snd) (by fun_prop)) measurable_const measurable_const
  have hHbound (p : ℝ × Θ) : ‖H p‖ ≤ 1 := by dsimp [H]; split_ifs <;> norm_num
  have hHint : Integrable H ((volume.restrict (Icc (-T) T)).prod ν) :=
    (MemLp.of_bound hH.aestronglyMeasurable 1 (ae_of_all _ hHbound) : MemLp _ 1 _).integrable (by norm_num)
  have hpoint (θ : Θ) : clippedLogarithm T (f θ) = T - ∫ s in Icc (-T) T, H (s, θ) :=
    clippedLogarithm_layer_cake T (f θ) hT (hf0 θ)
  simp_rw [hpoint]
  rw [integral_sub (integrable_const T) hHint.integral_prod_right,
    integral_const, probReal_univ, one_smul,
    ← integral_integral_swap (f := fun s θ => H (s, θ)) hHint]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s _
  change (∫ θ, if f θ ≤ Real.exp s then (1 : ℝ) else 0 ∂ν) = _
  have hset : MeasurableSet {θ | f θ ≤ Real.exp s} := measurableSet_le hf measurable_const
  exact integral_indicator_one hset

/-- The random-field layer-cake identity is pointwise in the random outcome. -/
theorem clippedLogarithmicIntegral_eq (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ × Ω → ℝ) (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    clippedLogarithmicIntegral ν X T ω = T - ∫ s in Icc (-T) T, levelOccupation ν X (s, ω) :=
  integral_clippedLogarithm_eq ν _ (hX.comp (measurable_id.prodMk measurable_const))
    (fun θ => hX0 (θ, ω)) T hT

/-- Uniform occupation variance bounds give `4 T² v` for the clipped logarithmic integral. -/
theorem variance_clippedLogarithmicIntegral_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p) (T : ℝ) (hT : 0 ≤ T)
    (v : ℝ) (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v) :
    variance (clippedLogarithmicIntegral ν X T) μ ≤ 4 * T ^ 2 * v := by
  have hA := measurable_levelOccupation ν X hX
  have hbound (p : ℝ × Ω) : ‖levelOccupation ν X p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (levelOccupation_mem_Icc ν X p).1]
    exact (levelOccupation_mem_Icc ν X p).2
  have heq : clippedLogarithmicIntegral ν X T =
      fun ω => T - ∫ s in Icc (-T) T, levelOccupation ν X (s, ω) := by
    ext ω
    exact clippedLogarithmicIntegral_eq ν X hX hX0 T hT ω
  rw [heq, variance_const_sub hA.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable]
  have h := variance_integral_le_mass_sq_mul μ (volume.restrict (Icc (-T) T))
    (levelOccupation ν X) hA 1 hbound v hvar
  simp only [measureReal_restrict_apply_univ, Real.volume_real_Icc,
    max_eq_left (by linarith : 0 ≤ T - -T)] at h
  convert h using 1
  ring

/-- Fubini expresses the mean clipped logarithm through mean occupations. -/
theorem integral_clippedLogarithmicIntegral_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, clippedLogarithmicIntegral ν X T ω ∂μ) =
      T - ∫ s in Icc (-T) T, ∫ ω, levelOccupation ν X (s, ω) ∂μ := by
  have hA := measurable_levelOccupation ν X hX
  have hbound (p : ℝ × Ω) : ‖levelOccupation ν X p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (levelOccupation_mem_Icc ν X p).1]
    exact (levelOccupation_mem_Icc ν X p).2
  have hI : Integrable (levelOccupation ν X) ((volume.restrict (Icc (-T) T)).prod μ) :=
    (MemLp.of_bound hA.aestronglyMeasurable 1 (ae_of_all _ hbound) : MemLp _ 1 _).integrable (by norm_num)
  simp_rw [clippedLogarithmicIntegral_eq ν X hX hX0 T hT]
  rw [integral_sub (integrable_const T) hI.integral_prod_right,
    integral_const, probReal_univ, one_smul,
    ← integral_integral_swap (f := fun s ω => levelOccupation ν X (s, ω)) hI]

/-- A uniform occupation bias `d` contributes at most `2 T d` after logarithmic clipping. -/
theorem integral_clippedLogarithmicIntegral_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p) (T : ℝ) (hT : 0 ≤ T)
    (q : ℝ → ℝ) (hq : Measurable q) (hqbound : ∀ s, ‖q s‖ ≤ 1)
    (d : ℝ) (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) - q s| ≤ d) :
    |(∫ ω, clippedLogarithmicIntegral ν X T ω ∂μ) -
      (T - ∫ s in Icc (-T) T, q s)| ≤ 2 * T * d := by
  let m : ℝ → ℝ := fun s => ∫ ω, levelOccupation ν X (s, ω) ∂μ
  have hm : Measurable m := (measurable_levelOccupation ν X hX).stronglyMeasurable.integral_prod_right'.measurable
  have hmbound (s : ℝ) : ‖m s‖ ≤ 1 := by
    apply (norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => levelOccupation ν X (s, ω)) (C := 1) ?_).trans_eq (by simp)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (levelOccupation_mem_Icc ν X (s, ω)).1]
    exact (levelOccupation_mem_Icc ν X (s, ω)).2
  have hmI : Integrable m (volume.restrict (Icc (-T) T)) :=
    (MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hmbound) : MemLp _ 1 _).integrable (by norm_num)
  have hqI : Integrable q (volume.restrict (Icc (-T) T)) :=
    (MemLp.of_bound hq.aestronglyMeasurable 1 (ae_of_all _ hqbound) : MemLp _ 1 _).integrable (by norm_num)
  rw [integral_clippedLogarithmicIntegral_eq μ ν X hX hX0 T hT]
  have hid : |(T - ∫ s in Icc (-T) T, m s) - (T - ∫ s in Icc (-T) T, q s)| =
      ‖∫ s in Icc (-T) T, m s - q s‖ := by
    rw [integral_sub hmI hqI, Real.norm_eq_abs, abs_sub_comm]
    congr 1
    ring
  rw [hid]
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (-T) T))
    (f := fun s => m s - q s) (C := d)
    (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hmean s)
  simp only [measureReal_restrict_apply_univ, Real.volume_real_Icc,
    max_eq_left (by linarith : 0 ≤ T - -T)] at h
  exact h.trans_eq (by ring)

/-- Chebyshev gives the clipped-log failure budget with its exact `4 T²` factor. -/
theorem measure_clippedLogarithmicIntegral_deviation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p) (T : ℝ) (hT : 0 ≤ T)
    (v : ℝ) (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (u : ℝ) (hu : 0 < u) :
    μ {ω | u ≤ |clippedLogarithmicIntegral ν X T ω - ∫ ω', clippedLogarithmicIntegral ν X T ω' ∂μ|} ≤
      ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := by
  have hLp : MemLp (clippedLogarithmicIntegral ν X T) 2 μ :=
    MemLp.of_bound (measurable_clippedLogarithmicIntegral ν X hX T).aestronglyMeasurable T
      (ae_of_all _ (norm_clippedLogarithmicIntegral_le ν X T hT))
  exact (meas_ge_le_variance_div_sq hLp hu).trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (variance_clippedLogarithmicIntegral_le μ ν X hX hX0 T hT v hvar)
      (sq_nonneg u)))

end Erdos522

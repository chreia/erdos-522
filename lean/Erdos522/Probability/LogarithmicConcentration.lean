/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.LogarithmicTails
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Logarithmic integral concentration

Occupation concentration, logarithmic moments, and quadratic energy together
control the unclipped logarithmic integral. The moment hypothesis remains
explicit, so that the theorem applies to each coefficient model supplying it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric

namespace Erdos522

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- The angular logarithmic second moment. -/
def logarithmicSquareIntegral (ν : Measure Θ) (X : Θ × Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ θ, |Real.log (X (θ, ω))| ^ 2 ∂ν

theorem measurable_logarithmicSquareIntegral (ν : Measure Θ) [SFinite ν]
    (X : Θ × Ω → ℝ) (hX : Measurable X) : Measurable (logarithmicSquareIntegral ν X) := by
  unfold logarithmicSquareIntegral
  simpa only [Real.norm_eq_abs] using
    (hX.log.norm.pow_const 2).stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace Ω] in
theorem logarithmicSquareIntegral_nonneg (ν : Measure Θ) (X : Θ × Ω → ℝ) (ω : Ω) :
    0 ≤ logarithmicSquareIntegral ν X ω := integral_nonneg fun _ => sq_nonneg _

omit [MeasurableSpace Ω] in
/-- Angular Jensen bounds a power of the logarithmic second moment by the corresponding log moment. -/
theorem logarithmicSquareIntegral_rpow_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ × Ω → ℝ) (ω : Ω) (q : ℝ) (hq : 1 ≤ q)
    (hlog : MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (hmoment : Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν) :
    logarithmicSquareIntegral ν X ω ^ q ≤ ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν := by
  have hid (θ : Θ) : (|Real.log (X (θ, ω))| ^ 2) ^ q = |Real.log (X (θ, ω))| ^ (2 * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hsq : Integrable (fun θ => |Real.log (X (θ, ω))| ^ 2) ν := by
    simpa only [Real.norm_eq_abs] using hlog.norm.integrable_sq
  have hpower : Integrable (fun θ => (|Real.log (X (θ, ω))| ^ 2) ^ q) ν := by
    simpa only [hid, logarithmicSquareIntegral] using hmoment
  have h := (convexOn_rpow hq).map_integral_le (Real.continuous_rpow_const (by linarith)).continuousOn
    isClosed_Ici (ae_of_all _ fun θ => sq_nonneg |Real.log (X (θ, ω))|) hsq hpower
  simpa only [hid, logarithmicSquareIntegral] using h

/-- A uniform logarithmic moment supplies the event controlling the angular `L²` logarithm. -/
theorem measure_logarithmicSquareIntegral_gt_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : 1 ≤ q)
    (hlog : ∀ ω, MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (hmoment : ∀ ω, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (D : ℝ) (hD : 0 < D) :
    μ {ω | D ^ 2 < logarithmicSquareIntegral ν X ω} ≤ ENNReal.ofReal (M / (D ^ 2) ^ q) := by
  have hU := measurable_logarithmicSquareIntegral ν X hX
  have hUq : Integrable (fun ω => logarithmicSquareIntegral ν X ω ^ q) μ := by
    apply hmomentI.mono' (hU.pow_const q).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (logarithmicSquareIntegral_nonneg ν X ω) q)]
    exact logarithmicSquareIntegral_rpow_le ν X ω q hq (hlog ω) (hmoment ω)
  have hmean : (∫ ω, logarithmicSquareIntegral ν X ω ^ q ∂μ) ≤ M :=
    (integral_mono hUq hmomentI (fun ω =>
      logarithmicSquareIntegral_rpow_le ν X ω q hq (hlog ω) (hmoment ω))).trans hM
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ fun ω => Real.rpow_nonneg (logarithmicSquareIntegral_nonneg ν X ω) q) hUq ((D ^ 2) ^ q)
  have hreal : μ.real {ω | (D ^ 2) ^ q ≤ logarithmicSquareIntegral ν X ω ^ q} ≤ M / (D ^ 2) ^ q :=
    (le_div_iff₀ (Real.rpow_pos_of_pos (sq_pos_of_pos hD) q)).mpr (by nlinarith [hmarkov])
  refine (measure_mono (t := {ω | (D ^ 2) ^ q ≤ logarithmicSquareIntegral ν X ω ^ q}) ?_).trans ?_
  · intro ω hω
    exact Real.rpow_le_rpow (sq_nonneg D) (le_of_lt hω) (by linarith)
  · rw [← ofReal_measureReal (μ := μ)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Occupation, logarithmic moments and a pathwise energy bound give explicit logarithmic concentration. -/
theorem logarithmic_integral_concentration (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (hXpos : ∀ ω, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (hlog : ∀ ω, MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (henergyI : ∀ ω, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (B : ℝ) (henergy : ∀ ω, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ ω, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    μ {ω | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ≤
      ENNReal.ofReal (v / b ^ 2 + M / (D ^ 2) ^ q + 4 * T ^ 2 * v / u ^ 2) := by
  let L := clippedLogarithmicIntegral ν X T
  let m := ∫ ω, L ω ∂μ
  let S := Real.exp (-2 * T) + d + b
  let E₁ : Set Ω := {ω | S < levelOccupation ν X (-T, ω)}
  let E₂ : Set Ω := {ω | D ^ 2 < logarithmicSquareIntegral ν X ω}
  let E₃ : Set Ω := {ω | u < |L ω - m|}
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hAbound (ω : Ω) : ‖levelOccupation ν X (-T, ω)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (levelOccupation_mem_Icc ν X (-T, ω)).1]
    exact (levelOccupation_mem_Icc ν X (-T, ω)).2
  have hALp : MemLp (fun ω => levelOccupation ν X (-T, ω)) 2 μ :=
    MemLp.of_bound ((measurable_levelOccupation ν X hX).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1 (ae_of_all _ hAbound)
  have hsmall : μ E₁ ≤ ENNReal.ofReal (v / b ^ 2) := by
    have hgauss := circularGaussian_real_closedBall_le_sq (Real.exp (-T)) (Real.exp_pos _).le
    have hexp : Real.exp (-T) ^ 2 = Real.exp (-2 * T) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [hexp] at hgauss
    refine (measure_mono ?_).trans ((meas_ge_le_variance_div_sq hALp hb).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hvar (-T)) (sq_nonneg b))))
    intro ω hω
    have hm := (abs_le.mp (hmean (-T))).2
    have ha := le_abs_self (levelOccupation ν X (-T, ω) - ∫ ω', levelOccupation ν X (-T, ω') ∂μ)
    change b ≤ |levelOccupation ν X (-T, ω) - ∫ ω', levelOccupation ν X (-T, ω') ∂μ|
    change Real.exp (-2 * T) + d + b < levelOccupation ν X (-T, ω) at hω
    linarith
  have hmomentBad : μ E₂ ≤ ENNReal.ofReal (M / (D ^ 2) ^ q) :=
    measure_logarithmicSquareIntegral_gt_le μ ν X hX q hq hlog hmoment hmomentI M hM D hD
  have hclipBad : μ E₃ ≤ ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := by
    refine (measure_mono ?_).trans (measure_clippedLogarithmicIntegral_deviation_le μ ν X hX hX0 T hT v hvar u hu)
    intro ω hω
    change u < |L ω - m| at hω
    exact le_of_lt hω
  have hclipBias : |m - circularClippedLogMean T| ≤ 2 * T * d := by
    rw [circularClippedLogMean_eq T hT]
    exact integral_clippedLogarithmicIntegral_error_le μ ν X hX hX0 T hT
      (fun s => circularGaussian.real (closedBall 0 (Real.exp s))) measurable_circularGaussian_exp_disk
      (fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one) d hmean
  have hsubset : {ω | u + 2 * T * d + D * Real.sqrt S + (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    intro ω hω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hSω : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ≤ S := le_of_not_gt h₁
    have hUω : logarithmicSquareIntegral ν X ω ≤ D ^ 2 := le_of_not_gt h₂
    have hLω : |L ω - m| ≤ u := le_of_not_gt h₃
    have hprod : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} * logarithmicSquareIntegral ν X ω ≤ S * D ^ 2 :=
      mul_le_mul hSω hUω (logarithmicSquareIntegral_nonneg ν X ω) hS
    have hsqrt : Real.sqrt (ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} * logarithmicSquareIntegral ν X ω) ≤
        D * Real.sqrt S := by
      have hh := Real.sqrt_le_sqrt hprod
      rw [Real.sqrt_mul hS, Real.sqrt_sq hD.le] at hh
      simpa only [mul_comm] using hh
    have hJL : |(∫ θ, Real.log (X (θ, ω)) ∂ν) - L ω| ≤
        D * Real.sqrt S + B / 2 * Real.exp (-2 * T) := by
      have hh := abs_integral_log_sub_clipped_le ν (fun θ => X (θ, ω))
        (hX.comp (measurable_id.prodMk measurable_const)) (hXpos ω) (hlog ω) (henergyI ω) T hT
      exact hh.trans (add_le_add hsqrt (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (henergy ω) (by norm_num)) (Real.exp_pos _).le))
    have hG := abs_circularLogMean_sub_clipped_le T hT
    rw [abs_sub_comm] at hG
    have h₄ := abs_sub_le (∫ θ, Real.log (X (θ, ω)) ∂ν) (L ω) circularLogMean
    have h₅ := abs_sub_le (L ω) m circularLogMean
    have h₆ := abs_sub_le m (circularClippedLogMean T) circularLogMean
    exfalso
    dsimp only [Set.mem_ofPred_eq] at hω
    nlinarith
  refine (measure_mono hsubset).trans ?_
  calc
    μ ((E₁ ∪ E₂) ∪ E₃) ≤ μ E₁ + μ E₂ + μ E₃ :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (le_refl _))
    _ ≤ ENNReal.ofReal (v / b ^ 2) + ENNReal.ofReal (M / (D ^ 2) ^ q) +
        ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := add_le_add (add_le_add hsmall hmomentBad) hclipBad
    _ = _ := by
      have hb0 : 0 ≤ v / b ^ 2 := div_nonneg hv (sq_nonneg b)
      have hm0 : 0 ≤ M / (D ^ 2) ^ q := div_nonneg hM0 (Real.rpow_nonneg (sq_nonneg D) q)
      have hu0 : 0 ≤ 4 * T ^ 2 * v / u ^ 2 := by positivity
      rw [ENNReal.ofReal_add (add_nonneg hb0 hm0) hu0, ENNReal.ofReal_add hb0 hm0]

/-- The normalized moment threshold produces exactly the power-law Markov budget. -/
theorem logarithmic_moment_failure_identity (A c β q : ℝ) (hA : 0 < A) (hc : 0 < c) :
    c ^ (2 * β * q) / ((A * c ^ β) ^ 2) ^ q = A ^ (-2 * q) := by
  have hden : ((A * c ^ β) ^ 2) ^ q = A ^ (2 * q) * c ^ (2 * β * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg hA.le (Real.rpow_nonneg hc.le β)),
      Real.mul_rpow hA.le (Real.rpow_nonneg hc.le β), ← Real.rpow_mul hc.le]
    congr 1
    congr 1
    ring
  rw [hden, show -2 * q = -(2 * q) by ring, Real.rpow_neg hA.le]
  have hcp : c ^ (2 * β * q) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  field_simp

end Erdos522

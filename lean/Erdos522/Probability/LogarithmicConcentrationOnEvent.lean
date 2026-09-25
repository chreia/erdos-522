/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicConcentration

/-!
# Logarithmic concentration on an energy event

Random coefficient amplitudes yield angular energy bounds on large events.
The occupation argument remains under the original probability measure;
only the deterministic positive-log tail is restricted to the energy event.
Logarithmic section assumptions are almost-everywhere statements.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace Erdos522
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- A uniform logarithmic moment supplies the event controlling the angular `L²` logarithm. -/
theorem measure_logarithmicSquareIntegral_gt_le_of_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : 1 ≤ q)
    (hlog : ∀ᵐ ω ∂μ, MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (hmoment : ∀ᵐ ω ∂μ, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (D : ℝ) (hD : 0 < D) :
    μ {ω | D ^ 2 < logarithmicSquareIntegral ν X ω} ≤ ENNReal.ofReal (M / (D ^ 2) ^ q) := by
  have hU := measurable_logarithmicSquareIntegral ν X hX
  have hUq : Integrable (fun ω => logarithmicSquareIntegral ν X ω ^ q) μ := by
    apply hmomentI.mono' (hU.pow_const q).aestronglyMeasurable
    filter_upwards [hlog, hmoment] with ω hlogω hmomentω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (logarithmicSquareIntegral_nonneg ν X ω) q)]
    exact logarithmicSquareIntegral_rpow_le ν X ω q hq hlogω hmomentω
  have hmean : (∫ ω, logarithmicSquareIntegral ν X ω ^ q ∂μ) ≤ M := by
    apply le_trans _ hM
    apply integral_mono_ae hUq hmomentI
    filter_upwards [hlog, hmoment] with ω hlogω hmomentω
    exact logarithmicSquareIntegral_rpow_le ν X ω q hq hlogω hmomentω
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ fun ω => Real.rpow_nonneg (logarithmicSquareIntegral_nonneg ν X ω) q) hUq ((D ^ 2) ^ q)
  have hreal : μ.real {ω | (D ^ 2) ^ q ≤ logarithmicSquareIntegral ν X ω ^ q} ≤ M / (D ^ 2) ^ q :=
    (le_div_iff₀ (Real.rpow_pos_of_pos (sq_pos_of_pos hD) q)).mpr (by nlinarith [hmarkov])
  refine (measure_mono (t := {ω | (D ^ 2) ^ q ≤ logarithmicSquareIntegral ν X ω ^ q}) ?_).trans ?_
  · intro ω hω
    exact Real.rpow_le_rpow (sq_nonneg D) (le_of_lt hω) (by linarith)
  · rw [← ofReal_measureReal (μ := μ)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Occupation and logarithmic moments concentrate the log integral on an event where the angular energy is bounded. -/
theorem logarithmic_integral_concentration_on_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (hXpos : ∀ᵐ ω ∂μ, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (hlog : ∀ᵐ ω ∂μ, MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (henergyI : ∀ᵐ ω ∂μ, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (A : Set Ω) (B : ℝ) (henergy : ∀ ω ∈ A, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ᵐ ω ∂μ, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    μ {ω | ω ∈ A ∧ u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
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
    measure_logarithmicSquareIntegral_gt_le_of_ae μ ν X hX q hq hlog hmoment hmomentI M hM D hD
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
  have hsubset : ∀ᵐ ω ∂μ, ω ∈ {ω | ω ∈ A ∧ u + 2 * T * d + D * Real.sqrt S + (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} → ω ∈ (E₁ ∪ E₂) ∪ E₃ := by
    filter_upwards [hXpos, hlog, henergyI] with ω hposω hlogω henergyIω
    rintro ⟨hAω, hω⟩
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
        (hX.comp (measurable_id.prodMk measurable_const)) hposω hlogω henergyIω T hT
      exact hh.trans (add_le_add hsqrt (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (henergy ω hAω) (by norm_num)) (Real.exp_pos _).le))
    have hG := abs_circularLogMean_sub_clipped_le T hT
    rw [abs_sub_comm] at hG
    have h₄ := abs_sub_le (∫ θ, Real.log (X (θ, ω)) ∂ν) (L ω) circularLogMean
    have h₅ := abs_sub_le (L ω) m circularLogMean
    have h₆ := abs_sub_le m (circularClippedLogMean T) circularLogMean
    exfalso
    nlinarith
  refine (measure_mono_ae hsubset).trans ?_
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


/-- Charging the complement of the energy event gives an unrestricted probability bound. -/
theorem logarithmic_integral_concentration_of_energy_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (hXpos : ∀ᵐ ω ∂μ, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (hlog : ∀ᵐ ω ∂μ, MemLp (fun θ => Real.log (X (θ, ω))) 2 ν)
    (henergyI : ∀ᵐ ω ∂μ, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (A : Set Ω) (B : ℝ) (henergy : ∀ ω ∈ A, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ᵐ ω ∂μ, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b D : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hD : 0 < D) :
    μ {ω | u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ≤
      μ Aᶜ + ENNReal.ofReal (v / b ^ 2 + M / (D ^ 2) ^ q + 4 * T ^ 2 * v / u ^ 2) := by
  have hbnd := logarithmic_integral_concentration_on_event μ ν X hX hX0 hXpos hlog henergyI A B henergy
    d v hd hv hmean hvar q hq hmoment hmomentI M hM0 hM T u b D hT hu hb hD
  refine (measure_mono (t := Aᶜ ∪ {ω | ω ∈ A ∧
      u + 2 * T * d + D * Real.sqrt (Real.exp (-2 * T) + d + b) +
        (B / 2 + 1) * Real.exp (-2 * T) <
        |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|}) ?_).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hbnd))
  intro ω hω
  by_cases hA : ω ∈ A
  · exact Or.inr ⟨hA, hω⟩
  · exact Or.inl hA

end Erdos522

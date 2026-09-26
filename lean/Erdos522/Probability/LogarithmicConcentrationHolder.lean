/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicConcentrationRestrictedMoments

/-!
# Logarithmic concentration through Hölder's inequality

The lower clipping error is the integral of `|log X|` over the small-value
event. Hölder's inequality with the exponents `2q` and `2q / (2q - 1)` bounds
it by the `2q`-th angular logarithmic moment `W` to the power `1 / (2q)`,
times the small-value occupation to the power `1 - 1 / (2q)`. Markov's
inequality for `W` then replaces the square-root bound of
`logarithmic_integral_concentration`, with the same occupation and energy
hypotheses.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric

namespace Erdos522

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- Restricting an `Lᵖ` norm to an event gains the power `1 - 1/p` of its mass. -/
theorem setIntegral_norm_le_holder {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (ν : Measure α) [IsFiniteMeasure ν] {f : α → E} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) ν) {s : Set α} (hs : MeasurableSet s) :
    (∫ a in s, ‖f a‖ ∂ν) ≤ (∫ a, ‖f a‖ ^ p ∂ν) ^ (1 / p) * ν.real s ^ (1 - 1 / p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hg : MemLp (s.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal (Real.conjExponent p)) ν :=
    (memLp_const (1 : ℝ)).indicator hs
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun a => norm_nonneg (f a))
    (ae_of_all _ fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a) hf.norm hg
  have hleft : (∫ a in s, ‖f a‖ ∂ν) = ∫ a, ‖f a‖ * s.indicator (fun _ => (1 : ℝ)) a ∂ν := by
    rw [← integral_indicator hs]
    congr 1
    funext a
    by_cases ha : a ∈ s <;> simp [ha]
  have hind : (∫ a, s.indicator (fun _ => (1 : ℝ)) a ^ Real.conjExponent p ∂ν) = ν.real s := by
    have hpow : (fun a => s.indicator (fun _ => (1 : ℝ)) a ^ Real.conjExponent p) =
        s.indicator 1 := by
      funext a
      by_cases ha : a ∈ s <;> simp [ha, Real.zero_rpow hpq.symm.ne_zero]
    rw [hpow, integral_indicator_one hs]
  have hexp : 1 / Real.conjExponent p = 1 - 1 / p := by
    rw [one_div, one_div, ← hpq.one_sub_inv]
  rw [hleft]
  calc
    _ ≤ _ := hH
    _ = _ := by rw [hind, hexp]

/-- The logarithmic integral differs from its clipping by at most the Hölder product plus the energy tail. -/
theorem abs_integral_log_sub_clipped_le_holder {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (f : Θ → ℝ) (hf : Measurable f)
    (hfpos : ∀ᵐ θ ∂ν, 0 < f θ) {p : ℝ} (hp : 1 < p)
    (hmoment : Integrable (fun θ => |Real.log (f θ)| ^ p) ν)
    (henergy : Integrable (fun θ => f θ ^ 2) ν) (T : ℝ) (hT : 0 ≤ T) :
    |(∫ θ, Real.log (f θ) ∂ν) - ∫ θ, clippedLogarithm T (f θ) ∂ν| ≤
      (∫ θ, |Real.log (f θ)| ^ p ∂ν) ^ (1 / p) *
          ν.real {θ | f θ ≤ Real.exp (-T)} ^ (1 - 1 / p) +
        ((∫ θ, f θ ^ 2 ∂ν) / 2) * Real.exp (-2 * T) := by
  have hlogm : AEStronglyMeasurable (fun θ => Real.log (f θ)) ν := hf.log.aestronglyMeasurable
  have hLp : MemLp (fun θ => Real.log (f θ)) (ENNReal.ofReal p) ν := by
    refine (integrable_norm_rpow_iff hlogm (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      ENNReal.ofReal_ne_top).mp ?_
    rw [ENNReal.toReal_ofReal (by linarith)]
    simpa only [Real.norm_eq_abs] using hmoment
  have hlogI : Integrable (fun θ => Real.log (f θ)) ν :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  let s : Set Θ := {θ | f θ ≤ Real.exp (-T)}
  have hs : MeasurableSet s := measurableSet_le hf measurable_const
  have hc : Integrable (fun θ => clippedLogarithm T (f θ)) ν := by
    apply (MemLp.of_bound ((measurable_clippedLogarithm T).comp hf).aestronglyMeasurable T ?_ :
      MemLp _ 1 ν).integrable (by norm_num)
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_le]
    exact clippedLogarithm_mem_Icc T _ hT
  have hlow : Integrable (s.indicator (fun θ => |Real.log (f θ)|)) ν := hlogI.abs.indicator hs
  have hupp : Integrable (fun θ => f θ ^ 2 / 2 * Real.exp (-2 * T)) ν :=
    (henergy.div_const 2).mul_const _
  have hholder := setIntegral_norm_le_holder ν hp hLp hs
  simp only [Real.norm_eq_abs] at hholder
  calc
    _ = |∫ θ, Real.log (f θ) - clippedLogarithm T (f θ) ∂ν| := by
      rw [integral_sub hlogI hc]
    _ ≤ ∫ θ, |Real.log (f θ) - clippedLogarithm T (f θ)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ θ, s.indicator (fun θ => |Real.log (f θ)|) θ + f θ ^ 2 / 2 * Real.exp (-2 * T) ∂ν := by
      apply integral_mono_ae (hlogI.sub hc).abs (hlow.add hupp)
      filter_upwards [hfpos] with θ hθ
      exact abs_log_sub_clippedLogarithm_le T (f θ) hT hθ
    _ = (∫ θ in s, |Real.log (f θ)| ∂ν) + ((∫ θ, f θ ^ 2 ∂ν) / 2) * Real.exp (-2 * T) := by
      rw [integral_add hlow hupp, integral_indicator hs, integral_mul_const, integral_div]
    _ ≤ _ := add_le_add hholder (le_refl _)

/-- The angular logarithmic moment of order `p`, the quantity `W` of the Hölder step for `p = 2q`. -/
def logarithmicMomentIntegral (ν : Measure Θ) (X : Θ × Ω → ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  ∫ θ, |Real.log (X (θ, ω))| ^ p ∂ν

theorem measurable_logarithmicMomentIntegral (ν : Measure Θ) [SFinite ν]
    (X : Θ × Ω → ℝ) (hX : Measurable X) (p : ℝ) :
    Measurable (logarithmicMomentIntegral ν X p) := by
  unfold logarithmicMomentIntegral
  simpa only [Real.norm_eq_abs] using
    (hX.log.norm.pow_const p).stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace Ω] in
theorem logarithmicMomentIntegral_nonneg (ν : Measure Θ) (X : Θ × Ω → ℝ) (p : ℝ) (ω : Ω) :
    0 ≤ logarithmicMomentIntegral ν X p ω :=
  integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p

/-- Markov's inequality for the angular logarithmic moment: the Markov event for `W`. -/
theorem measure_logarithmicMomentIntegral_gt_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure Θ) (X : Θ × Ω → ℝ) (p : ℝ)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ p ∂ν) μ)
    (M : ℝ) (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ p ∂ν ∂μ) ≤ M)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    μ {ω | Λ ^ p < logarithmicMomentIntegral ν X p ω} ≤ ENNReal.ofReal (M / Λ ^ p) := by
  have hWI : Integrable (logarithmicMomentIntegral ν X p) μ := hmomentI
  have hM' : (∫ ω, logarithmicMomentIntegral ν X p ω ∂μ) ≤ M := hM
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ (logarithmicMomentIntegral_nonneg ν X p)) hWI (Λ ^ p)
  have hreal : μ.real {ω | Λ ^ p ≤ logarithmicMomentIntegral ν X p ω} ≤ M / Λ ^ p := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hΛ p), mul_comm]
    exact hmarkov.trans hM'
  refine (measure_mono (t := {ω | Λ ^ p ≤ logarithmicMomentIntegral ν X p ω}) ?_).trans ?_
  · intro ω hω
    change Λ ^ p < logarithmicMomentIntegral ν X p ω at hω
    change Λ ^ p ≤ logarithmicMomentIntegral ν X p ω
    exact le_of_lt hω
  · rw [← ofReal_measureReal (μ := μ)]
    exact ENNReal.ofReal_le_ofReal hreal

omit [MeasurableSpace Ω] in
/-- Off the Markov event for `W` and the Chebyshev event for the small-value occupation,
the Hölder product is at most `Λ S ^ (1 - 1/(2q))`. -/
theorem holder_product_le (ν : Measure Θ) (X : Θ × Ω → ℝ) (ω : Ω) (q : ℝ) (hq : 1 ≤ q)
    (T S Λ : ℝ) (hΛ : 0 < Λ)
    (hSω : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ≤ S)
    (hWω : logarithmicMomentIntegral ν X (2 * q) ω ≤ Λ ^ (2 * q)) :
    (∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) ^ (1 / (2 * q)) *
        ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ^ (1 - 1 / (2 * q)) ≤
      Λ * S ^ (1 - 1 / (2 * q)) := by
  have hq2 : 0 < 2 * q := by linarith
  have hexp0 : 0 ≤ 1 - 1 / (2 * q) := by
    have : 1 / (2 * q) ≤ 1 := (div_le_one hq2).mpr (by linarith)
    linarith
  have hW1 : logarithmicMomentIntegral ν X (2 * q) ω ^ (1 / (2 * q)) ≤ Λ := by
    calc
      _ ≤ (Λ ^ (2 * q)) ^ (1 / (2 * q)) :=
        Real.rpow_le_rpow (logarithmicMomentIntegral_nonneg ν X (2 * q) ω) hWω (by positivity)
      _ = Λ := by rw [one_div, Real.rpow_rpow_inv hΛ.le hq2.ne']
  have hA1 : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ^ (1 - 1 / (2 * q)) ≤ S ^ (1 - 1 / (2 * q)) :=
    Real.rpow_le_rpow measureReal_nonneg hSω hexp0
  exact mul_le_mul hW1 hA1 (Real.rpow_nonneg measureReal_nonneg _) hΛ.le

/-- Occupation, logarithmic moments and a pathwise energy bound give explicit logarithmic
concentration, with the lower clipping error bounded through Hölder's inequality. -/
theorem logarithmic_integral_concentration_holder (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (hXpos : ∀ ω, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (henergyI : ∀ ω, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (B : ℝ) (henergy : ∀ ω, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ ω, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : Integrable (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b Λ : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hΛ : 0 < Λ) :
    μ {ω | u + 2 * T * d + Λ * (Real.exp (-2 * T) + d + b) ^ (1 - 1 / (2 * q)) +
        (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ≤
      ENNReal.ofReal (v / b ^ 2 + M / Λ ^ (2 * q) + 4 * T ^ 2 * v / u ^ 2) := by
  let L := clippedLogarithmicIntegral ν X T
  let m := ∫ ω, L ω ∂μ
  let S := Real.exp (-2 * T) + d + b
  let E₁ : Set Ω := {ω | S < levelOccupation ν X (-T, ω)}
  let E₂ : Set Ω := {ω | Λ ^ (2 * q) < logarithmicMomentIntegral ν X (2 * q) ω}
  let E₃ : Set Ω := {ω | u < |L ω - m|}
  have hp : 1 < 2 * q := by linarith
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
  have hmomentBad : μ E₂ ≤ ENNReal.ofReal (M / Λ ^ (2 * q)) :=
    measure_logarithmicMomentIntegral_gt_le μ ν X (2 * q) hmomentI M hM Λ hΛ
  have hclipBad : μ E₃ ≤ ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := by
    refine (measure_mono ?_).trans
      (measure_clippedLogarithmicIntegral_deviation_le μ ν X hX hX0 T hT v hvar u hu)
    intro ω hω
    change u < |L ω - m| at hω
    exact le_of_lt hω
  have hclipBias : |m - circularClippedLogMean T| ≤ 2 * T * d := by
    rw [circularClippedLogMean_eq T hT]
    exact integral_clippedLogarithmicIntegral_error_le μ ν X hX hX0 T hT
      (fun s => circularGaussian.real (closedBall 0 (Real.exp s))) measurable_circularGaussian_exp_disk
      (fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
      d hmean
  have hsubset : {ω | u + 2 * T * d + Λ * S ^ (1 - 1 / (2 * q)) + (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    intro ω hω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hSω : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ≤ S := le_of_not_gt h₁
    have hWω : logarithmicMomentIntegral ν X (2 * q) ω ≤ Λ ^ (2 * q) := le_of_not_gt h₂
    have hLω : |L ω - m| ≤ u := le_of_not_gt h₃
    have hholder := holder_product_le ν X ω q hq T S Λ hΛ hSω hWω
    have hJL : |(∫ θ, Real.log (X (θ, ω)) ∂ν) - L ω| ≤
        Λ * S ^ (1 - 1 / (2 * q)) + B / 2 * Real.exp (-2 * T) := by
      have hh := abs_integral_log_sub_clipped_le_holder ν (fun θ => X (θ, ω))
        (hX.comp (measurable_id.prodMk measurable_const)) (hXpos ω) hp (hmoment ω) (henergyI ω) T hT
      exact hh.trans (add_le_add hholder (mul_le_mul_of_nonneg_right
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
    _ ≤ ENNReal.ofReal (v / b ^ 2) + ENNReal.ofReal (M / Λ ^ (2 * q)) +
        ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := add_le_add (add_le_add hsmall hmomentBad) hclipBad
    _ = _ := by
      have hb0 : 0 ≤ v / b ^ 2 := div_nonneg hv (sq_nonneg b)
      have hm0 : 0 ≤ M / Λ ^ (2 * q) := div_nonneg hM0 (Real.rpow_nonneg hΛ.le _)
      have hu0 : 0 ≤ 4 * T ^ 2 * v / u ^ 2 := by positivity
      rw [ENNReal.ofReal_add (add_nonneg hb0 hm0) hu0, ENNReal.ofReal_add hb0 hm0]

/-- The Hölder form of logarithmic concentration on an event where the angular energy is
bounded, with logarithmic moments required only on that event. -/
theorem logarithmic_integral_concentration_restricted_moments_holder (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (A : Set Ω) (hA : MeasurableSet A)
    (hXpos : ∀ᵐ ω ∂μ.restrict A, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (henergyI : ∀ᵐ ω ∂μ.restrict A, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (B : ℝ) (henergy : ∀ ω ∈ A, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ᵐ ω ∂μ.restrict A, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : IntegrableOn (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) A μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω in A, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b Λ : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hΛ : 0 < Λ) :
    μ {ω | ω ∈ A ∧ u + 2 * T * d + Λ * (Real.exp (-2 * T) + d + b) ^ (1 - 1 / (2 * q)) +
        (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ≤
      ENNReal.ofReal (v / b ^ 2 + M / Λ ^ (2 * q) + 4 * T ^ 2 * v / u ^ 2) := by
  let L := clippedLogarithmicIntegral ν X T
  let m := ∫ ω, L ω ∂μ
  let S := Real.exp (-2 * T) + d + b
  let E₁ : Set Ω := {ω | S < levelOccupation ν X (-T, ω)}
  let E₂ : Set Ω := A ∩ {ω | Λ ^ (2 * q) < logarithmicMomentIntegral ν X (2 * q) ω}
  let E₃ : Set Ω := {ω | u < |L ω - m|}
  have hp : 1 < 2 * q := by linarith
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
  have hmomentBad : μ E₂ ≤ ENNReal.ofReal (M / Λ ^ (2 * q)) := by
    have h := measure_logarithmicMomentIntegral_gt_le (μ.restrict A) ν X (2 * q) hmomentI M hM Λ hΛ
    rw [Measure.restrict_apply (measurableSet_lt measurable_const
      (measurable_logarithmicMomentIntegral ν X hX (2 * q)))] at h
    simpa only [E₂, Set.inter_comm] using h
  have hclipBad : μ E₃ ≤ ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := by
    refine (measure_mono ?_).trans
      (measure_clippedLogarithmicIntegral_deviation_le μ ν X hX hX0 T hT v hvar u hu)
    intro ω hω
    change u < |L ω - m| at hω
    exact le_of_lt hω
  have hclipBias : |m - circularClippedLogMean T| ≤ 2 * T * d := by
    rw [circularClippedLogMean_eq T hT]
    exact integral_clippedLogarithmicIntegral_error_le μ ν X hX hX0 T hT
      (fun s => circularGaussian.real (closedBall 0 (Real.exp s))) measurable_circularGaussian_exp_disk
      (fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
      d hmean
  have hsubset : ∀ᵐ ω ∂μ, ω ∈ {ω | ω ∈ A ∧ u + 2 * T * d + Λ * S ^ (1 - 1 / (2 * q)) +
      (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} → ω ∈ (E₁ ∪ E₂) ∪ E₃ := by
    filter_upwards [(ae_restrict_iff' hA).mp hXpos, (ae_restrict_iff' hA).mp hmoment,
      (ae_restrict_iff' hA).mp henergyI] with ω hposω hmomentω henergyIω
    rintro ⟨hAω, hω⟩
    have hposω := hposω hAω
    have hmomentω := hmomentω hAω
    have henergyIω := henergyIω hAω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hSω : ν.real {θ | X (θ, ω) ≤ Real.exp (-T)} ≤ S := le_of_not_gt h₁
    have hWω : logarithmicMomentIntegral ν X (2 * q) ω ≤ Λ ^ (2 * q) :=
      le_of_not_gt (fun hh => h₂ ⟨hAω, hh⟩)
    have hLω : |L ω - m| ≤ u := le_of_not_gt h₃
    have hholder := holder_product_le ν X ω q hq T S Λ hΛ hSω hWω
    have hJL : |(∫ θ, Real.log (X (θ, ω)) ∂ν) - L ω| ≤
        Λ * S ^ (1 - 1 / (2 * q)) + B / 2 * Real.exp (-2 * T) := by
      have hh := abs_integral_log_sub_clipped_le_holder ν (fun θ => X (θ, ω))
        (hX.comp (measurable_id.prodMk measurable_const)) hposω hp hmomentω henergyIω T hT
      exact hh.trans (add_le_add hholder (mul_le_mul_of_nonneg_right
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
    _ ≤ ENNReal.ofReal (v / b ^ 2) + ENNReal.ofReal (M / Λ ^ (2 * q)) +
        ENNReal.ofReal (4 * T ^ 2 * v / u ^ 2) := add_le_add (add_le_add hsmall hmomentBad) hclipBad
    _ = _ := by
      have hb0 : 0 ≤ v / b ^ 2 := div_nonneg hv (sq_nonneg b)
      have hm0 : 0 ≤ M / Λ ^ (2 * q) := div_nonneg hM0 (Real.rpow_nonneg hΛ.le _)
      have hu0 : 0 ≤ 4 * T ^ 2 * v / u ^ 2 := by positivity
      rw [ENNReal.ofReal_add (add_nonneg hb0 hm0) hu0, ENNReal.ofReal_add hb0 hm0]

/-- Charging the complement of the energy event gives the unrestricted Hölder bound. -/
theorem logarithmic_integral_concentration_of_restricted_moments_holder (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ν : Measure Θ) [IsProbabilityMeasure ν] (X : Θ × Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ p, 0 ≤ X p)
    (A : Set Ω) (hA : MeasurableSet A)
    (hXpos : ∀ᵐ ω ∂μ.restrict A, ∀ᵐ θ ∂ν, 0 < X (θ, ω))
    (henergyI : ∀ᵐ ω ∂μ.restrict A, Integrable (fun θ => X (θ, ω) ^ 2) ν)
    (B : ℝ) (henergy : ∀ ω ∈ A, (∫ θ, X (θ, ω) ^ 2 ∂ν) ≤ B)
    (d v : ℝ) (hv : 0 ≤ v)
    (hmean : ∀ s, |(∫ ω, levelOccupation ν X (s, ω) ∂μ) -
      circularGaussian.real (closedBall 0 (Real.exp s))| ≤ d)
    (hvar : ∀ s, variance (fun ω => levelOccupation ν X (s, ω)) μ ≤ v)
    (q : ℝ) (hq : 1 ≤ q)
    (hmoment : ∀ᵐ ω ∂μ.restrict A, Integrable (fun θ => |Real.log (X (θ, ω))| ^ (2 * q)) ν)
    (hmomentI : IntegrableOn (fun ω => ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν) A μ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ ω in A, ∫ θ, |Real.log (X (θ, ω))| ^ (2 * q) ∂ν ∂μ) ≤ M)
    (T u b Λ : ℝ) (hT : 0 ≤ T) (hu : 0 < u) (hb : 0 < b) (hΛ : 0 < Λ) :
    μ {ω | u + 2 * T * d + Λ * (Real.exp (-2 * T) + d + b) ^ (1 - 1 / (2 * q)) +
        (B / 2 + 1) * Real.exp (-2 * T) <
      |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|} ≤
      μ Aᶜ + ENNReal.ofReal (v / b ^ 2 + M / Λ ^ (2 * q) + 4 * T ^ 2 * v / u ^ 2) := by
  have hbnd := logarithmic_integral_concentration_restricted_moments_holder μ ν X hX hX0 A hA
    hXpos henergyI B henergy d v hv hmean hvar q hq hmoment hmomentI M hM0 hM T u b Λ
    hT hu hb hΛ
  refine (measure_mono (t := Aᶜ ∪ {ω | ω ∈ A ∧
      u + 2 * T * d + Λ * (Real.exp (-2 * T) + d + b) ^ (1 - 1 / (2 * q)) +
        (B / 2 + 1) * Real.exp (-2 * T) <
        |(∫ θ, Real.log (X (θ, ω)) ∂ν) - circularLogMean|}) ?_).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hbnd))
  intro ω hω
  by_cases hA : ω ∈ A
  · exact Or.inr ⟨hA, hω⟩
  · exact Or.inl hA

/-- With `Λ = λ (2Cq)^β` and the moment budget `M = (2Cq)^(2βq)`, the Markov failure
probability for `W` is `λ^(-2q)`. -/
theorem logarithmic_moment_holder_failure_identity (A c β q : ℝ) (hA : 0 < A) (hc : 0 < c) :
    c ^ (2 * β * q) / (A * c ^ β) ^ (2 * q) = A ^ (-2 * q) := by
  have hden : (A * c ^ β) ^ (2 * q) = A ^ (2 * q) * c ^ (2 * β * q) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hc.le β), ← Real.rpow_mul hc.le]
    congr 1
    congr 1
    ring
  rw [hden, show -2 * q = -(2 * q) by ring, Real.rpow_neg hA.le]
  have hcp : c ^ (2 * β * q) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  field_simp

end Erdos522

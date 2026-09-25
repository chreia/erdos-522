/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ClippedLogarithm
import Erdos522.Analysis.PartitionAverages

/-!
# Recovering logarithmic integrals from clipped logarithms

The upper clipping tail is controlled by quadratic energy. The lower tail
is controlled by the logarithmic second moment and small-value occupation.
-/

noncomputable section
open MeasureTheory Set

namespace Erdos522

/-- Quadratic energy controls the amount removed above the clipping interval. -/
theorem log_sub_clippedLogarithm_le (T x : ℝ) (hT : 0 ≤ T) (hx : 0 < x) :
    Real.log x - clippedLogarithm T x ≤ x ^ 2 / 2 * Real.exp (-2 * T) := by
  rw [clippedLogarithm, ite_eq_right (not_le.mpr hx)]
  by_cases hxt : Real.log x ≤ T
  · have h : Real.log x ≤ max (-T) (min T (Real.log x)) := by
      rw [min_eq_right hxt]
      exact le_max_right _ _
    exact (sub_nonpos.mpr h).trans (by positivity)
  · have htx : T ≤ Real.log x := le_of_lt (lt_of_not_ge hxt)
    rw [min_eq_left htx, max_eq_right (by linarith : -T ≤ T)]
    have he := Real.add_one_le_exp (2 * (Real.log x - T))
    have heq : Real.exp (2 * (Real.log x - T)) = x ^ 2 * Real.exp (-2 * T) := by
      rw [show 2 * (Real.log x - T) = Real.log x + Real.log x + (-2 * T) by ring,
        Real.exp_add, Real.exp_add, Real.exp_log hx]
      ring
    rw [heq] at he
    nlinarith

/-- The lower clipping error is supported on the small-value event. -/
theorem clippedLogarithm_sub_log_le (T x : ℝ) (hT : 0 ≤ T) (hx : 0 < x) :
    clippedLogarithm T x - Real.log x ≤
      if x ≤ Real.exp (-T) then |Real.log x| else 0 := by
  rw [clippedLogarithm, ite_eq_right (not_le.mpr hx)]
  by_cases hsmall : x ≤ Real.exp (-T)
  · rw [ite_eq_left hsmall]
    have hxlog : Real.log x ≤ -T := (Real.log_le_iff_le_exp hx).mpr hsmall
    rw [min_eq_right (by linarith : Real.log x ≤ T), max_eq_left hxlog,
      abs_of_nonpos (by linarith : Real.log x ≤ 0)]
    linarith
  · rw [ite_eq_right hsmall]
    apply sub_nonpos.mpr
    apply max_le
    · have h : ¬ Real.log x ≤ -T := fun h => hsmall ((Real.log_le_iff_le_exp hx).mp h)
      linarith
    · exact min_le_right _ _

/-- Both clipping errors are bounded pointwise by an energy term and a small-value term. -/
theorem abs_log_sub_clippedLogarithm_le (T x : ℝ) (hT : 0 ≤ T) (hx : 0 < x) :
    |Real.log x - clippedLogarithm T x| ≤
      (if x ≤ Real.exp (-T) then |Real.log x| else 0) + x ^ 2 / 2 * Real.exp (-2 * T) := by
  have hpos := log_sub_clippedLogarithm_le T x hT hx
  have hneg := clippedLogarithm_sub_log_le T x hT hx
  have hsmall : 0 ≤ if x ≤ Real.exp (-T) then |Real.log x| else 0 := by split_ifs <;> positivity
  have henergy : 0 ≤ x ^ 2 / 2 * Real.exp (-2 * T) := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Restricting an `L²` norm to an event gains the square root of the event's mass. -/
theorem integral_norm_restrict_le_sqrt {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (ν : Measure Ω) [IsFiniteMeasure ν] {f : Ω → E} (hf : MemLp f 2 ν) (s : Set Ω) :
    (∫ ω in s, ‖f ω‖ ∂ν) ≤ Real.sqrt (ν.real s * ∫ ω, ‖f ω‖ ^ 2 ∂ν) := by
  have h := sq_integral_norm_le_mass_mul_integral_sq (hf.restrict s)
  rw [measureReal_restrict_apply_univ] at h
  have hmono : (∫ ω in s, ‖f ω‖ ^ 2 ∂ν) ≤ ∫ ω, ‖f ω‖ ^ 2 ∂ν :=
    integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun ω => sq_nonneg _) hf.norm.integrable_sq
  have hsq := h.trans (mul_le_mul_of_nonneg_left hmono measureReal_nonneg)
  exact (Real.le_sqrt (integral_nonneg fun _ => norm_nonneg _) (by positivity)).mpr hsq

/-- The logarithmic integral differs from its clipping by at most `sqrt(U S)` plus the energy tail. -/
theorem abs_integral_log_sub_clipped_le {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (f : Θ → ℝ) (hf : Measurable f)
    (hfpos : ∀ᵐ θ ∂ν, 0 < f θ) (hlog : MemLp (fun θ => Real.log (f θ)) 2 ν)
    (henergy : Integrable (fun θ => f θ ^ 2) ν) (T : ℝ) (hT : 0 ≤ T) :
    |(∫ θ, Real.log (f θ) ∂ν) - ∫ θ, clippedLogarithm T (f θ) ∂ν| ≤
      Real.sqrt ((ν.real {θ | f θ ≤ Real.exp (-T)}) * ∫ θ, |Real.log (f θ)| ^ 2 ∂ν) +
        ((∫ θ, f θ ^ 2 ∂ν) / 2) * Real.exp (-2 * T) := by
  let s : Set Θ := {θ | f θ ≤ Real.exp (-T)}
  have hs : MeasurableSet s := measurableSet_le hf measurable_const
  have hc : Integrable (fun θ => clippedLogarithm T (f θ)) ν := by
    apply (MemLp.of_bound ((measurable_clippedLogarithm T).comp hf).aestronglyMeasurable T ?_ : MemLp _ 1 ν).integrable (by norm_num)
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_le]
    exact clippedLogarithm_mem_Icc T _ hT
  have hlow : Integrable (s.indicator (fun θ => |Real.log (f θ)|)) ν :=
    (hlog.integrable (by norm_num)).abs.indicator hs
  have hupp : Integrable (fun θ => f θ ^ 2 / 2 * Real.exp (-2 * T)) ν :=
    (henergy.div_const 2).mul_const _
  have hsqrt := integral_norm_restrict_le_sqrt ν hlog s
  simp only [Real.norm_eq_abs] at hsqrt
  calc
    _ = |∫ θ, Real.log (f θ) - clippedLogarithm T (f θ) ∂ν| := by
      rw [integral_sub (hlog.integrable (by norm_num)) hc]
    _ ≤ ∫ θ, |Real.log (f θ) - clippedLogarithm T (f θ)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ θ, s.indicator (fun θ => |Real.log (f θ)|) θ + f θ ^ 2 / 2 * Real.exp (-2 * T) ∂ν := by
      apply integral_mono_ae ((hlog.integrable (by norm_num)).sub hc).abs (hlow.add hupp)
      filter_upwards [hfpos] with θ hθ
      exact abs_log_sub_clippedLogarithm_le T (f θ) hT hθ
    _ = (∫ θ in s, |Real.log (f θ)| ∂ν) + ((∫ θ, f θ ^ 2 ∂ν) / 2) * Real.exp (-2 * T) := by
      rw [integral_add hlow hupp, integral_indicator hs, integral_mul_const, integral_div]
    _ ≤ _ := add_le_add hsqrt (le_refl _)

end Erdos522

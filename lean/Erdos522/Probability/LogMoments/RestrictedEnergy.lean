/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Sublevel bounds from restricted quadratic energy

A logarithmic loss in a restricted energy inequality gives a quantitative
bound on the measure of exponentially small values.
-/

noncomputable section

open MeasureTheory Set

namespace Erdos522
namespace LogMoments

theorem ae_ne_zero_of_restrictedEnergy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℂ} {A : ℝ} (hf : Measurable f)
    (hE : ∀ E : Set Ω, MeasurableSet E → 0 < μ.real E →
      1 ≤ Real.exp (A * Real.log (2 / μ.real E) ^ 6) * ∫ ω in E, ‖f ω‖ ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, f ω ≠ 0 := by
  have hmeas : MeasurableSet {ω | f ω = 0} := hf (measurableSet_singleton 0)
  have hzero : (∫ ω in {ω | f ω = 0}, ‖f ω‖ ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hmeas] with ω hω
    simp [hω]
  have hreal : μ.real {ω | f ω = 0} = 0 := by
    by_contra h
    have hpos := (measureReal_nonneg (μ := μ) (s := {ω | f ω = 0})).lt_of_ne' h
    have he := hE _ hmeas hpos
    rw [hzero, mul_zero] at he
    norm_num at he
  rw [ae_iff]
  simpa only [not_not] using (measureReal_eq_zero_iff).mp hreal

theorem sublevel_measure_le_of_restrictedEnergy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℂ} {A : ℝ} (hA : 0 < A) (hf : Measurable f)
    (hI : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hE : ∀ E : Set Ω, MeasurableSet E → 0 < μ.real E →
      1 ≤ Real.exp (A * Real.log (2 / μ.real E) ^ 6) * ∫ ω in E, ‖f ω‖ ^ 2 ∂μ)
    {s : ℝ} (hs : 0 < s) :
    μ.real {ω | ‖f ω‖ ≤ Real.exp (-A * s ^ 6)} ≤ 2 * Real.exp (-s) := by
  let E := {ω | ‖f ω‖ ≤ Real.exp (-A * s ^ 6)}
  have hmeas : MeasurableSet E := measurableSet_le hf.norm measurable_const
  have hδone : μ.real E ≤ 1 := measureReal_le_one
  by_contra! hbad
  have hδ : 0 < μ.real E := lt_trans (by positivity) hbad
  have hlog_nonneg : 0 ≤ Real.log (2 / μ.real E) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hlog_lt : Real.log (2 / μ.real E) < s := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
    have hb : 2 / Real.exp s < μ.real E := by
      simpa only [Real.exp_neg, div_eq_mul_inv] using hbad
    have hm := (div_lt_iff₀ (Real.exp_pos s)).mp hb
    exact (div_lt_iff₀ hδ).mpr (by simpa only [mul_comm] using hm)
  have hpow : Real.log (2 / μ.real E) ^ 6 < s ^ 6 := by
    gcongr
  have hbound : (∫ ω in E, ‖f ω‖ ^ 2 ∂μ) ≤ Real.exp (-2 * A * s ^ 6) := by
    calc
      (∫ ω in E, ‖f ω‖ ^ 2 ∂μ) ≤ ∫ _ω in E, (Real.exp (-A * s ^ 6)) ^ 2 ∂μ := by
        apply setIntegral_mono_on hI.integrableOn (integrable_const _) hmeas
        intro ω hω
        exact pow_le_pow_left₀ (norm_nonneg _) hω 2
      _ = μ.real E * (Real.exp (-A * s ^ 6)) ^ 2 := by simp [integral_const]
      _ ≤ 1 * (Real.exp (-A * s ^ 6)) ^ 2 :=
        mul_le_mul_of_nonneg_right hδone (sq_nonneg _)
      _ = Real.exp (-2 * A * s ^ 6) := by
        rw [one_mul, sq, ← Real.exp_add]
        congr 1
        ring
  have h := (hE E hmeas hδ).trans
    (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le)
  rw [← Real.exp_add, Real.one_le_exp_iff] at h
  have hsmall := mul_lt_mul_of_pos_left hpow hA
  have hpos := mul_pos hA (pow_pos hs 6)
  nlinarith

end LogMoments
end Erdos522

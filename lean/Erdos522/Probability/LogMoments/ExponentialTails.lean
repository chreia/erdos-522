/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Exponential integrals from exponential tails

Layer-cake integration converts a tail bound into an integrable exponential
with an explicit integral bound.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos522
namespace LogMoments

theorem integral_half_exp (y : ℝ) :
    (∫ s in 0..y, (1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s)) =
      Real.exp ((1 / 2 : ℝ) * y) - 1 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (1 / 2 : ℝ) ≠ 0),
    integral_exp]
  norm_num
  ring

theorem lintegral_exp_half_sub_one_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ s : ℝ, 0 < s → μ {ω | s ≤ Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-s))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * Y ω) - 1) ∂μ) ≤ 2 := by
  have hc := lintegral_comp_eq_lintegral_meas_le_mul μ (ae_of_all _ hY0)
    hY.aemeasurable
    (g := fun s : ℝ => (1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s))
    (fun _ _ => Continuous.intervalIntegrable (by fun_prop) _ _)
    (ae_of_all _ (fun _ => by positivity))
  simp only [integral_half_exp] at hc
  rw [hc]
  calc
    (∫⁻ s in Ioi (0 : ℝ), μ {ω | s ≤ Y ω} *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s))) ≤
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp ((-1 / 2 : ℝ) * s)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      calc
        μ {ω | s ≤ Y ω} * ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s)) ≤
            ENNReal.ofReal (2 * Real.exp (-s)) *
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s)) :=
          mul_le_mul_left (htail s hs) _
        _ = ENNReal.ofReal (Real.exp ((-1 / 2 : ℝ) * s)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          calc
            (2 * Real.exp (-s)) * ((1 / 2 : ℝ) * Real.exp ((1 / 2 : ℝ) * s)) =
                Real.exp (-s) * Real.exp ((1 / 2 : ℝ) * s) := by ring
            _ = Real.exp ((-1 / 2 : ℝ) * s) := by
              rw [← Real.exp_add]
              congr 1
              ring
    _ = 2 := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0)
        (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
        integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
      norm_num

theorem integrable_exp_half_and_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ s : ℝ, 0 < s → μ {ω | s ≤ Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-s))) :
    Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * Y ω)) μ ∧
      (∫ ω, Real.exp ((1 / 2 : ℝ) * Y ω) ∂μ) ≤ 3 := by
  have hm : Measurable (fun ω => Real.exp ((1 / 2 : ℝ) * Y ω) - 1) := by fun_prop
  have hn : ∀ ω, 0 ≤ Real.exp ((1 / 2 : ℝ) * Y ω) - 1 := by
    intro ω
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (hY0 ω)))
  have hbound := lintegral_exp_half_sub_one_le hY hY0 htail
  have hI : Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * Y ω) - 1) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (ae_of_all _ hn)).mp
      (ne_top_of_le_ne_top (by norm_num) hbound)
  have hreal : (∫ ω, Real.exp ((1 / 2 : ℝ) * Y ω) - 1 ∂μ) ≤ 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hn)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp (by simpa using hbound)
  have heq : (fun ω => Real.exp ((1 / 2 : ℝ) * Y ω)) =
      (fun ω => Real.exp ((1 / 2 : ℝ) * Y ω) - 1) + (fun _ => 1) := by
    ext ω
    simp
  rw [heq]
  constructor
  · exact hI.add (integrable_const 1)
  · change (∫ ω, (Real.exp ((1 / 2 : ℝ) * Y ω) - 1) + 1 ∂μ) ≤ 3
    rw [integral_add hI (integrable_const 1)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith

end LogMoments
end Erdos522

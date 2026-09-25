/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# First moments from exponential probability tails

A nonnegative random variable with tail bounded by `a exp (-b s)` is
integrable with first moment at most `a / b`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Erdos522

/-- Layer cake integrates an exponential tail with its exact constant. -/
theorem integrable_and_integral_le_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (htail : ∀ s : ℝ, 0 < s → μ {ω | s ≤ Y ω} ≤ ENNReal.ofReal (a * Real.exp (-b * s))) :
    Integrable Y μ ∧ (∫ ω, Y ω ∂μ) ≤ a / b := by
  have hbound : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≤ ENNReal.ofReal (a / b) := by
    rw [lintegral_eq_lintegral_meas_le μ (ae_of_all _ hY0) hY.aemeasurable]
    calc
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (a * Real.exp (-b * s)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact htail s hs
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).const_mul a)
          (ae_of_all _ fun _ => mul_nonneg ha (Real.exp_pos _).le),
          integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb) 0]
        congr 1
        simp
        ring
  have hI : Integrable Y μ :=
    (lintegral_ofReal_ne_top_iff_integrable hY.aestronglyMeasurable (ae_of_all _ hY0)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hY0)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg ha hb.le)).mp hbound

end Erdos522

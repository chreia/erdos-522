/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.BinaryEntropy
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Entropy bounds for event probabilities

Mapping a probability space to the indicator of a measurable event reduces
relative entropy to its binary form. The quadratic binary entropy bound then
controls the difference of event probabilities.
-/

noncomputable section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace Erdos522

/-- At an atom of positive reference mass, the real Radon--Nikodym derivative
    is the ratio of the two atom masses. -/
theorem toReal_rnDeriv_at_atom {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (x : α)
    (hνx : 0 < ν.real {x}) :
    (μ.rnDeriv ν x).toReal = μ.real {x} / ν.real {x} := by
  have h := Measure.setLIntegral_rnDeriv hμν ({x} : Set α)
  rw [lintegral_singleton] at h
  have hr := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ← measureReal_def] at hr
  exact (eq_div_iff hνx.ne').mpr hr

/-- The two masses of a Boolean probability law add to one. -/
theorem measureReal_bool_false (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ.real {false} = 1 - μ.real {true} := by
  have hc : ({true} : Set Bool)ᶜ = {false} := by
    ext b
    cases b <;> simp
  have h := measureReal_compl (μ := μ) (measurableSet_singleton true)
  simpa only [hc, probReal_univ] using h

/-- Relative entropy of Boolean probability laws has the binary logarithmic formula. -/
theorem toReal_klDiv_bool (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (hv0 : 0 < ν.real {true}) (hv1 : ν.real {true} < 1) :
    (klDiv μ ν).toReal = binaryRelativeEntropy (μ.real {true}) (ν.real {true}) := by
  have hvfalse : 0 < ν.real {false} := by
    rw [measureReal_bool_false]
    linarith
  have hrtrue := toReal_rnDeriv_at_atom hμν true hv0
  have hrfalse := toReal_rnDeriv_at_atom hμν false hvfalse
  rw [toReal_klDiv_of_measure_eq hμν (by rw [measure_univ, measure_univ]), integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, smul_eq_mul, llr, hrtrue, hrfalse,
    measureReal_bool_false, binaryRelativeEntropy]

/-- Relative entropy bounds the difference of the two Boolean event probabilities. -/
theorem two_mul_sq_bool_probability_sub_le_klDiv (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * (μ.real {true} - ν.real {true}) ^ 2) ≤ klDiv μ ν := by
  by_cases htop : klDiv μ ν = ∞
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  by_cases hv0 : ν.real {true} = 0
  · have hνzero : ν {true} = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hv0
    have hμzero : μ.real {true} = 0 := (measureReal_eq_zero_iff (by finiteness)).mpr (hac hνzero)
    simp [hμzero, hv0]
  by_cases hv1 : ν.real {true} = 1
  · have hνfalse : ν.real {false} = 0 := by rw [measureReal_bool_false, hv1]; norm_num
    have hνzero : ν {false} = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hνfalse
    have hμfalse : μ.real {false} = 0 := (measureReal_eq_zero_iff (by finiteness)).mpr (hac hνzero)
    have hμone : μ.real {true} = 1 := by rw [measureReal_bool_false] at hμfalse; linarith
    simp [hμone, hv1]
  have hvpos : 0 < ν.real {true} := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hv0)
  have hvlt : ν.real {true} < 1 := lt_of_le_of_ne measureReal_le_one hv1
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  rw [toReal_klDiv_bool μ ν hac hvpos hvlt]
  exact binaryRelativeEntropy_ge_two_mul_sq measureReal_nonneg measureReal_le_one hvpos hvlt

/-- The sharp event-probability entropy inequality for arbitrary probability measures. -/
theorem two_mul_sq_measureReal_sub_le_klDiv {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set α) (hE : MeasurableSet E) :
    ENNReal.ofReal (2 * (μ.real E - ν.real E) ^ 2) ≤ klDiv μ ν := by
  classical
  let flag : α → Bool := fun x => if x ∈ E then true else false
  have hflag : Measurable flag := Measurable.ite hE measurable_const measurable_const
  have hpre : flag ⁻¹' {true} = E := by
    ext x
    simp [flag]
  have h := (two_mul_sq_bool_probability_sub_le_klDiv (μ.map flag) (ν.map flag)).trans
    (klDiv_map_le μ ν hflag)
  simpa only [map_measureReal_apply hflag (measurableSet_singleton true), hpre] using h

/-- The square-root form of the event-probability entropy bound. -/
theorem abs_measureReal_sub_le_sqrt_half_klDiv {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set α) (hE : MeasurableSet E) (hfinite : klDiv μ ν ≠ ∞) :
    |μ.real E - ν.real E| ≤ Real.sqrt ((klDiv μ ν).toReal / 2) := by
  have h := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    (two_mul_sq_measureReal_sub_le_klDiv μ ν E hE)
  have hs : (μ.real E - ν.real E) ^ 2 ≤ (klDiv μ ν).toReal / 2 := by linarith
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hs

/-- A finite upper bound on relative entropy gives a uniform bound for every event. -/
theorem abs_measureReal_sub_le_of_klDiv_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : 0 ≤ B) (hkl : klDiv μ ν ≤ ENNReal.ofReal B)
    (E : Set α) (hE : MeasurableSet E) :
    |μ.real E - ν.real E| ≤ Real.sqrt (B / 2) := by
  have hfinite : klDiv μ ν ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hreal : (klDiv μ ν).toReal ≤ B := by
    have h := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hkl
    simpa only [ENNReal.toReal_ofReal hB] using h
  exact (abs_measureReal_sub_le_sqrt_half_klDiv μ ν E hE hfinite).trans
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hreal (by norm_num)))

end Erdos522

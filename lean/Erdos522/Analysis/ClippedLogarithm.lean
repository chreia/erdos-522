/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Clipped logarithms and their level sets

Clipping the logarithm makes it bounded, including at zero. Its integral
is expressed through small-value occupations over a finite interval of levels.
-/

noncomputable section
open MeasureTheory Set

namespace Erdos522

/-- The logarithm clipped to `[-T,T]`, with the lower clipping value at nonpositive inputs. -/
def clippedLogarithm (T x : ℝ) : ℝ :=
  if x ≤ 0 then -T else max (-T) (min T (Real.log x))

/-- A clipped logarithm is a measurable function of its nonnegative radius. -/
theorem measurable_clippedLogarithm (T : ℝ) : Measurable (clippedLogarithm T) := by
  unfold clippedLogarithm
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  fun_prop

/-- The clipped logarithm always belongs to its clipping interval. -/
theorem clippedLogarithm_mem_Icc (T x : ℝ) (hT : 0 ≤ T) :
    clippedLogarithm T x ∈ Icc (-T) T := by
  unfold clippedLogarithm
  split_ifs
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The layer-cake identity for clipping a real level. -/
theorem clip_level_layer_cake (T y : ℝ) (hT : 0 ≤ T) :
    max (-T) (min T y) = T - ∫ s in Icc (-T) T, (Ici y).indicator (fun _ => (1 : ℝ)) s := by
  rw [integral_indicator_const (μ := volume.restrict (Icc (-T) T)) 1 measurableSet_Ici,
    measureReal_restrict_apply measurableSet_Ici, smul_eq_mul, mul_one]
  have hset : Ici y ∩ Icc (-T) T = Icc (max y (-T)) T := by
    ext s
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [hset, Real.volume_real_Icc]
  by_cases hy : y ≤ -T
  · have hyT : y ≤ T := by linarith
    rw [min_eq_right hyT, max_eq_left hy, max_eq_right hy,
      max_eq_left (by linarith : 0 ≤ T - -T)]
    ring
  · have hy' : -T ≤ y := le_of_lt (lt_of_not_ge hy)
    by_cases hyT : y ≤ T
    · rw [min_eq_right hyT, max_eq_right hy', max_eq_left hy',
        max_eq_left (sub_nonneg.mpr hyT)]
      ring
    · have hTy : T ≤ y := le_of_lt (lt_of_not_ge hyT)
      rw [min_eq_left hTy, max_eq_right (by linarith : -T ≤ T), max_eq_left hy',
        max_eq_right (sub_nonpos.mpr hTy), sub_zero]

/-- The logarithmic layer-cake identity uses the closed sublevel event `x ≤ exp(s)`. -/
theorem clippedLogarithm_layer_cake (T x : ℝ) (hT : 0 ≤ T) (hx : 0 ≤ x) :
    clippedLogarithm T x = T - ∫ s in Icc (-T) T, if x ≤ Real.exp s then (1 : ℝ) else 0 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [clippedLogarithm, le_refl, ite_eq_left, (Real.exp_pos _).le]
    simp only [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Icc,
      smul_eq_mul, mul_one, max_eq_left (by linarith : 0 ≤ T - -T)]
    ring
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [clippedLogarithm, ite_eq_right (not_le.mpr hxpos), clip_level_layer_cake T (Real.log x) hT]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro s _
    simp only [Set.indicator, mem_Ici, Real.log_le_iff_le_exp hxpos]

end Erdos522

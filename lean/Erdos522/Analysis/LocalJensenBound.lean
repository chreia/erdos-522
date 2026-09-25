/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.JensenSecants
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-!
# Local Jensen bounds for polynomial zeros

A nonzero value at the center and a supremum bound on a larger circle control
all zeros in the smaller closed disk, counted with multiplicity.
-/

noncomputable section

open Polynomial

namespace Erdos522

/-- The logarithmic circle average dominates the logarithm at a nonzero center. -/
theorem log_norm_eval_zero_le_logCircleAverage (P : Polynomial ℂ)
    (hP : P.eval 0 ≠ 0) (r : ℝ) :
    Real.log ‖P.eval 0‖ ≤ logCircleAverage P r := by
  let Q := P.comp (C (r : ℂ) * X)
  have hnorm : ‖P.eval 0‖ ≤ Q.mahlerMeasure := by
    simpa [Q, Polynomial.coeff_zero_eq_eval_zero] using
      Polynomial.norm_coeff_le_choose_mul_mahlerMeasure 0 Q
  rw [logCircleAverage_eq_logMahlerMeasure, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr hP) hnorm

/-- A circle supremum bounds the logarithmic circle average. -/
theorem logCircleAverage_le_log_bound (P : Polynomial ℂ) {r M : ℝ}
    (hM : 1 ≤ M) (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, ‖P.eval z‖ ≤ M) :
    logCircleAverage P r ≤ Real.log M := by
  apply Real.circleAverage_mono_on_of_le_circle
  · exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) P).mono (Set.subset_univ _)).meromorphicOn.circleIntegrable_log_norm
  · intro z hz
    rcases eq_or_lt_of_le (norm_nonneg (P.eval z)) with hzero | hpos
    · rw [← hzero, Real.log_zero]
      exact Real.log_nonneg hM
    · exact Real.log_le_log hpos (hbound z hz)

/-- Jensen's bound in a smaller closed disk, with every root counted with multiplicity. -/
theorem closedZeroCount_le_log_bound (P : Polynomial ℂ) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hP : P.eval 0 ≠ 0)
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖P.eval z‖ ≤ M) :
    (closedZeroCount P r : ℝ) ≤
      (Real.log M - Real.log ‖P.eval 0‖) / Real.log (R / r) := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hu := logCircleAverage_le_log_bound P (r := R) hM (by simpa only [abs_of_pos (hr.trans hrR)] using hbound)
  have hl := log_norm_eval_zero_le_logCircleAverage P hP r
  apply (radial_zero_count_bound P hr hrR).1.trans
  apply div_le_div_of_nonneg_right _ hlog.le
  linarith

/-- Translation of a polynomial preserves the multiplicities in a translated closed disk. -/
theorem closedZeroCount_comp_translate (P : Polynomial ℂ) (c : ℂ) (r : ℝ) :
    closedZeroCount (P.comp (X + C c)) r = zeroCountIn P (Metric.closedBall c r) := by
  classical
  have hroots : (P.comp (X + C c)).roots = P.roots.map (fun z => z - c) := by
    simpa using Polynomial.roots_comp_C_mul_X_add_C P 1 c isUnit_one
  simp only [closedZeroCount, zeroCountIn, hroots, Multiset.filter_map, Multiset.card_map]
  congr 2
  ext z
  simp only [Function.comp_apply, Set.mem_ofPred, Metric.mem_closedBall, dist_eq_norm]

/-- A local Jensen bound centered at an arbitrary nonzero polynomial value. -/
theorem local_zero_count_bound (P : Polynomial ℂ) (c : ℂ) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hP : P.eval c ≠ 0)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖P.eval z‖ ≤ M) :
    (zeroCountIn P (Metric.closedBall c r) : ℝ) ≤
      (Real.log M - Real.log ‖P.eval c‖) / Real.log (R / r) := by
  rw [← closedZeroCount_comp_translate P c r]
  have h := closedZeroCount_le_log_bound (P.comp (X + C c)) hr hrR hM
    (by simpa using hP) (by
      intro z hz
      simp only [eval_comp, eval_add, eval_X, eval_C]
      apply hbound
      simpa only [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz)
  simpa using h

end Erdos522

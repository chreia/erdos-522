/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.RadialProfileRegularity

/-!
# The explicit Kac radial distribution

Away from the origin the profile has its elementary geometric-series formula.
At the origin its continuous value is one half.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The explicit derivative of the logarithmic variance profile away from zero. -/
theorem kacRadialProfile_eq {x : ℝ} (hx : x ≠ 0) :
    kacRadialProfile x = Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x) := by
  have hx2 : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have he : Real.exp (2 * x) - 1 ≠ 0 := by
    intro h
    have h' : Real.exp (2 * x) = 1 := by linarith
    have hlog := congrArg Real.log h'
    rw [Real.log_exp, Real.log_one] at hlog
    exact hx2 hlog
  have hn : HasDerivAt (fun y : ℝ => Real.exp (2 * y) - 1) (Real.exp (2 * x) * 2) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul 2).exp.sub_const 1
  have hd : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul 2
  have hquot := hn.div hd hx2
  have hlog := (hquot.log (div_ne_zero he hx2)).const_mul (1 / 2 : ℝ)
  simp only [Pi.div_apply] at hlog
  have hformula : (1 / 2 : ℝ) *
      (((Real.exp (2 * x) * 2 * (2 * x) - (Real.exp (2 * x) - 1) * 2) / (2 * x) ^ 2) /
        ((Real.exp (2 * x) - 1) / (2 * x))) =
      Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x) := by
    field_simp
  rw [hformula] at hlog
  have hF : HasDerivAt kacLogVarianceProfile
      (Real.exp (2 * x) / (Real.exp (2 * x) - 1) - 1 / (2 * x)) x := by
    apply hlog.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [kacLogVarianceProfile, kacVarianceProfile, hy]
  exact hF.deriv

/-- Reflection of the limiting radial distribution about the unit circle. -/
theorem kacRadialProfile_reflection (x : ℝ) :
    kacRadialProfile x + kacRadialProfile (-x) = 1 := by
  have hd := (differentiableAt_kacLogVarianceProfile x).hasDerivAt
  have hn := (differentiableAt_kacLogVarianceProfile (-x)).hasDerivAt.comp x (hasDerivAt_id x).neg
  have href := (hasDerivAt_id x).add hn
  have heq : (fun y : ℝ => y + kacLogVarianceProfile (-y)) = kacLogVarianceProfile :=
    funext fun y => (kacLogVarianceProfile_reflection y).symm
  change HasDerivAt (fun y : ℝ => y + kacLogVarianceProfile (-y))
    (1 + deriv kacLogVarianceProfile (-x) * -1) x at href
  rw [heq] at href
  have he := hd.unique href
  unfold kacRadialProfile
  linarith

end Erdos522

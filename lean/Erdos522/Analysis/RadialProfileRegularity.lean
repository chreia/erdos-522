/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.KacProfileDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity of the Kac radial profile

The derivative of the logarithmic variance profile is the limiting radial
distribution function. Its continuity allows convergence at rational radial
coordinates to extend to every real coordinate.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The limiting radial distribution function. -/
def kacRadialProfile (x : ℝ) : ℝ := deriv kacLogVarianceProfile x

theorem kacRadialProfile_zero : kacRadialProfile 0 = (1 / 2 : ℝ) :=
  hasDerivAt_kacLogVarianceProfile_zero.deriv

/-- A shifted two-scale secant converges to the derivative for any differentiable function. -/
theorem tendsto_two_scale_secant {f : ℝ → ℝ} {x d s : ℝ}
    (hf : HasDerivAt f d x) (hs : s ≠ 0) :
    Tendsto (fun m : ℕ => (f (x + 2 * (s / ((m : ℝ) + 1))) -
      f (x + s / ((m : ℝ) + 1))) / (s / ((m : ℝ) + 1))) atTop (𝓝 d) := by
  let h : ℕ → ℝ := fun m => s / ((m : ℝ) + 1)
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [h, mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul s
  have hc := (continuousAt_dslope_same.mpr hf.differentiableAt).tendsto
  rw [dslope_same, hf.deriv] at hc
  have hd : Tendsto (fun m => dslope f x (x + 2 * h m)) atTop (𝓝 d) := by
    exact hc.comp (by simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (ht.const_mul 2))
  have hsingle : Tendsto (fun m => dslope f x (x + h m)) atTop (𝓝 d) := by
    exact hc.comp (by simpa only [add_zero] using tendsto_const_nhds.add ht)
  have hsum : Tendsto (fun m => 2 * dslope f x (x + 2 * h m) - dslope f x (x + h m))
      atTop (𝓝 d) := by
    simpa only [show (2 : ℝ) * d - d = d by ring] using (hd.const_mul (2 : ℝ)).sub hsingle
  apply hsum.congr
  intro m
  have hh : h m ≠ 0 := div_ne_zero hs (by positivity)
  have h₁ : x + h m ≠ x := by exact add_ne_left.mpr hh
  have h₂ : x + 2 * h m ≠ x := add_ne_left.mpr (mul_ne_zero (by norm_num) hh)
  rw [dslope_of_ne _ h₁, dslope_of_ne _ h₂]
  simp only [slope_def_field, add_sub_cancel_left]
  dsimp only [h]
  field_simp
  ring

/-- The divided exponential difference is analytic at the removable singularity. -/
theorem analyticAt_kacVarianceProfile (x : ℝ) : AnalyticAt ℝ kacVarianceProfile x := by
  by_cases hx : x = 0
  · subst x
    obtain ⟨p, hp⟩ := (analyticAt_rexp (x := 0))
    have ha : AnalyticAt ℝ (dslope Real.exp 0) (2 * (0 : ℝ)) := by
      simpa only [mul_zero] using hp.has_fpower_series_dslope_fslope.analyticAt
    have heq : kacVarianceProfile = fun x => dslope Real.exp 0 (2 * x) :=
      funext kacVarianceProfile_eq_dslope
    rw [heq]
    exact ha.comp (analyticAt_const.mul analyticAt_id)
  · have ha : AnalyticAt ℝ (fun y : ℝ => (Real.exp (2 * y) - 1) / (2 * y)) x := by
      exact ((analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id)).sub analyticAt_const).div
        (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hx)
    apply ha.congr
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [kacVarianceProfile, hy]

/-- The logarithmic profile is continuously differentiable. -/
theorem contDiff_kacLogVarianceProfile : ContDiff ℝ 1 kacLogVarianceProfile := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hl : ContDiffAt ℝ 1 (fun x => Real.log (kacVarianceProfile x)) x :=
    (analyticAt_kacVarianceProfile x).contDiffAt.log (kacVarianceProfile_pos x).ne'
  exact contDiffAt_const.mul hl

theorem continuous_kacRadialProfile : Continuous kacRadialProfile :=
  contDiff_kacLogVarianceProfile.continuous_deriv_one

end Erdos522

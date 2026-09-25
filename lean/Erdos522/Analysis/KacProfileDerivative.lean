/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.KacVarianceProfile
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of the radial variance profile

The apparent singularity of the geometric formula at zero is the removable
singularity of the divided exponential difference. Reflection then identifies
the derivative of the logarithmic profile at the origin.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The continuous geometric variance profile is a divided exponential difference. -/
theorem kacVarianceProfile_eq_dslope (x : ℝ) :
    kacVarianceProfile x = dslope Real.exp 0 (2 * x) := by
  by_cases hx : x = 0
  · simp [hx, kacVarianceProfile, Real.deriv_exp]
  · have hx2 : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
    rw [dslope_of_ne _ hx2]
    simp [kacVarianceProfile, hx, slope_def_field, div_eq_mul_inv, mul_comm]

/-- The Kac variance profile is differentiable at every real radial coordinate. -/
theorem differentiableAt_kacVarianceProfile (x : ℝ) :
    DifferentiableAt ℝ kacVarianceProfile x := by
  have hd : DifferentiableAt ℝ (dslope Real.exp 0) (2 * x) := by
    by_cases hx : x = 0
    · subst x
      obtain ⟨p, hp⟩ := (analyticAt_rexp (x := 0))
      simpa only [mul_zero] using hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
    · exact (differentiableAt_dslope_of_ne (mul_ne_zero (by norm_num) hx)).mpr
        (Real.differentiable_exp.differentiableAt)
  have heq : kacVarianceProfile = fun x => dslope Real.exp 0 (2 * x) := funext kacVarianceProfile_eq_dslope
  rw [heq]
  exact hd.comp x ((hasDerivAt_id x).const_mul 2).differentiableAt

/-- Positivity of the variance profile makes its logarithm differentiable everywhere. -/
theorem differentiableAt_kacLogVarianceProfile (x : ℝ) :
    DifferentiableAt ℝ kacLogVarianceProfile x := by
  exact ((differentiableAt_kacVarianceProfile x).log (kacVarianceProfile_pos x).ne').const_mul (1 / 2 : ℝ)

/-- Reflection fixes the logarithmic variance derivative at the origin. -/
theorem hasDerivAt_kacLogVarianceProfile_zero :
    HasDerivAt kacLogVarianceProfile (1 / 2 : ℝ) 0 := by
  have hd := (differentiableAt_kacLogVarianceProfile 0).hasDerivAt
  have hn : HasDerivAt (fun x : ℝ => kacLogVarianceProfile (-x))
      (-deriv kacLogVarianceProfile 0) 0 := by
    have hd' : HasDerivAt kacLogVarianceProfile (deriv kacLogVarianceProfile 0) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hd
    simpa only [mul_neg_one, Function.comp_def] using hd'.comp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg
  have heq : (fun x : ℝ => x + kacLogVarianceProfile (-x)) = kacLogVarianceProfile := by
    funext x
    exact (kacLogVarianceProfile_reflection x).symm
  have href := (hasDerivAt_id (0 : ℝ)).add hn
  change HasDerivAt (fun x : ℝ => x + kacLogVarianceProfile (-x))
    (1 + -deriv kacLogVarianceProfile 0) 0 at href
  rw [heq] at href
  have hv : deriv kacLogVarianceProfile 0 = (1 / 2 : ℝ) := by linarith [hd.unique href]
  exact hv ▸ hd

/-- Two shrinking noncentral secants converge to the derivative at the origin.
The sign of `s` chooses the side of the origin. -/
theorem tendsto_kac_profile_two_scale_secant {s : ℝ} (hs : s ≠ 0) :
    Tendsto (fun m : ℕ =>
      (kacLogVarianceProfile (2 * (s / ((m : ℝ) + 1))) -
        kacLogVarianceProfile (s / ((m : ℝ) + 1))) / (s / ((m : ℝ) + 1)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  let h : ℕ → ℝ := fun m => s / ((m : ℝ) + 1)
  have ht : Tendsto h atTop (𝓝 0) := by
    simpa only [h, mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul s
  have hc := (continuousAt_dslope_same.mpr
    hasDerivAt_kacLogVarianceProfile_zero.differentiableAt).tendsto
  rw [dslope_same, hasDerivAt_kacLogVarianceProfile_zero.deriv] at hc
  have hd : Tendsto (fun m => dslope kacLogVarianceProfile 0 (2 * h m)) atTop (𝓝 (1 / 2 : ℝ)) := by
    exact hc.comp (by simpa only [mul_zero] using ht.const_mul 2)
  have hsingle := hc.comp ht
  have hsum : Tendsto (fun m => 2 * dslope kacLogVarianceProfile 0 (2 * h m) -
      dslope kacLogVarianceProfile 0 (h m)) atTop (𝓝 (1 / 2 : ℝ)) := by
    convert (hd.const_mul 2).sub hsingle using 1 <;> norm_num
  apply hsum.congr
  intro m
  have hh : h m ≠ 0 := div_ne_zero hs (by positivity)
  have h₂ : 2 * h m ≠ 0 := mul_ne_zero (by norm_num) hh
  rw [dslope_of_ne _ hh, dslope_of_ne _ h₂]
  simp only [slope_def_field, sub_zero]
  change 2 * ((kacLogVarianceProfile (2 * h m) - kacLogVarianceProfile 0) / (2 * h m)) -
      (kacLogVarianceProfile (h m) - kacLogVarianceProfile 0) / h m = _
  dsimp only [h]
  field_simp
  ring

end Erdos522

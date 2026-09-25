/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Erdos522.Analysis.HolomorphicZeroCount

/-!
# Lower bounds for zero-free holomorphic functions

Poisson's formula compares a nonnegative harmonic function with its value at
the center of a disk. Applied to the logarithmic defect from an outer modulus
bound, this gives quantitative lower bounds for a zero-free holomorphic
function on smaller disks.
-/

noncomputable section
open Complex InnerProductSpace Metric Real Set
namespace Erdos522

/-- Integrating upper and lower bounds for the Poisson kernel compares a
nonnegative harmonic function with its central value. -/
theorem harmonic_comparison_of_kernel_bounds {u : ℂ → ℝ} {c w : ℂ} {R a b : ℝ}
    (hu : HarmonicOnNhd u (closedBall c R)) (hw : w ∈ ball c R)
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z)
    (hlower : ∀ z ∈ sphere c R, a ≤ (herglotzRieszKernel c w z).re)
    (hupper : ∀ z ∈ sphere c R, (herglotzRieszKernel c w z).re ≤ b) :
    a * u c ≤ u w ∧ u w ≤ b * u c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hus : ContinuousOn u (sphere c |R|) := by
    rw [abs_of_pos hR]
    exact hu.continuousOn.mono sphere_subset_closedBall
  have hwne : w ∉ sphere c |R| := by
    rw [abs_of_pos hR]
    intro h
    have := mem_ball.mp hw
    have := mem_sphere.mp h
    linarith
  have hki : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel c w) • u) c R :=
    ((Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hwne)).smul hus).circleIntegrable'
  have hla : CircleIntegrable (a • u) c R := (continuousOn_const.smul hus).circleIntegrable'
  have hub : CircleIntegrable (b • u) c R := (continuousOn_const.smul hus).circleIntegrable'
  have hav : circleAverage u c R = u c := (show HarmonicOnNhd u (closedBall c |R|) by simpa only [abs_of_pos hR] using hu).circleAverage_eq
  have hlo := circleAverage_mono hla hki (fun z hz => by
    have hz' : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
    exact mul_le_mul_of_nonneg_right (hlower z hz') (hnonneg z hz'))
  have hhi := circleAverage_mono hki hub (fun z hz => by
    have hz' : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
    exact mul_le_mul_of_nonneg_right (hupper z hz') (hnonneg z hz'))
  rw [circleAverage_smul, hu.circleAverage_re_herglotzRieszKernel_smul hw, hav] at hlo
  rw [circleAverage_smul, hu.circleAverage_re_herglotzRieszKernel_smul hw, hav] at hhi
  exact ⟨hlo, hhi⟩

/-- Harnack's inequalities on a disk, with the exact radial factors. Boundary
nonnegativity suffices, by Poisson's formula. -/
theorem harmonic_harnack {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall c R)) (hw : w ∈ ball c R)
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * u c ≤ u w ∧
      u w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * u c := by
  exact harmonic_comparison_of_kernel_bounds hu hw hnonneg
    (fun z hz => le_re_herglotzRieszKernel hz hw)
    (fun z hz => re_herglotzRieszKernel_le hz hw)

/-- On the half-radius disk, the Harnack factors are `1/3` and `3`. -/
theorem harmonic_harnack_half_disk {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : HarmonicOnNhd u (closedBall c R))
    (hw : w ∈ closedBall c (R / 2)) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z) :
    u c / 3 ≤ u w ∧ u w ≤ 3 * u c := by
  have hd : ‖w - c‖ ≤ R / 2 := mem_closedBall_iff_norm.mp hw
  have hw' : w ∈ ball c R := mem_ball_iff_norm.mpr (by linarith)
  have hden : 0 < R - ‖w - c‖ := by linarith
  have hsum : 0 < R + ‖w - c‖ := by positivity
  have h := harmonic_comparison_of_kernel_bounds hu hw' hnonneg (a := 1 / 3) (b := 3)
    (fun z hz => (show (1 : ℝ) / 3 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) by
      apply (le_div_iff₀ hsum).mpr
      linarith).trans (le_re_herglotzRieszKernel hz hw'))
    (fun z hz => (re_herglotzRieszKernel_le hz hw').trans (by
      apply (div_le_iff₀ hden).mpr
      linarith))
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- Values at any two points of the half-radius disk differ by at most the
factor `9` for a nonnegative harmonic function. -/
theorem harmonic_harnack_two_points_half_disk {u : ℂ → ℝ} {c v w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : HarmonicOnNhd u (closedBall c R))
    (hv : v ∈ closedBall c (R / 2)) (hw : w ∈ closedBall c (R / 2))
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z) : u w ≤ 9 * u v := by
  have hv' := (harmonic_harnack_half_disk hR hu hv hnonneg).1
  have hw' := (harmonic_harnack_half_disk hR hu hw hnonneg).2
  linarith

/-- Uniform Harnack bounds on any concentric smaller disk. -/
theorem harmonic_harnack_inner_disk {u : ℂ → ℝ} {c w : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hu : HarmonicOnNhd u (closedBall c R))
    (hw : w ∈ closedBall c r) (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z) :
    (R - r) / (R + r) * u c ≤ u w ∧
      u w ≤ (R + r) / (R - r) * u c := by
  have hR : 0 < R := hr.trans_lt hrR
  have hd : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw' : w ∈ ball c R := mem_ball_iff_norm.mpr (hd.trans_lt hrR)
  have hden : 0 < R - ‖w - c‖ := by linarith
  have hsum : 0 < R + ‖w - c‖ := by positivity
  exact harmonic_comparison_of_kernel_bounds hu hw' hnonneg
    (fun z hz => (show (R - r) / (R + r) ≤ (R - ‖w - c‖) / (R + ‖w - c‖) by
      rw [div_le_div_iff₀ (by positivity : 0 < R + r) hsum]
      nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hd)]).trans
        (le_re_herglotzRieszKernel hz hw'))
    (fun z hz => (re_herglotzRieszKernel_le hz hw').trans (by
      rw [div_le_div_iff₀ hden (sub_pos.mpr hrR)]
      nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hd)]))

/-- A two-point Harnack comparison on a concentric smaller disk. -/
theorem harmonic_harnack_two_points_inner_disk {u : ℂ → ℝ} {c v w : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hu : HarmonicOnNhd u (closedBall c R))
    (hv : v ∈ closedBall c r) (hw : w ∈ closedBall c r)
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ u z) :
    u w ≤ ((R + r) / (R - r)) ^ 2 * u v := by
  have hlo := (harmonic_harnack_inner_disk hr hrR hu hv hnonneg).1
  have hhi := (harmonic_harnack_inner_disk hr hrR hu hw hnonneg).2
  have hR : 0 < R := hr.trans_lt hrR
  have hfactor : 0 < (R + r) / (R - r) := div_pos (by positivity) (sub_pos.mpr hrR)
  have hproduct : (R + r) / (R - r) * ((R - r) / (R + r)) = 1 := by
    field_simp [(sub_pos.mpr hrR).ne', (show 0 < R + r by positivity).ne']
  have hcenter := mul_le_mul_of_nonneg_left hlo hfactor.le
  rw [← mul_assoc, hproduct, one_mul] at hcenter
  calc
    _ ≤ (R + r) / (R - r) * u c := hhi
    _ ≤ (R + r) / (R - r) * ((R + r) / (R - r) * u v) :=
      mul_le_mul_of_nonneg_left hcenter hfactor.le
    _ = _ := by ring

/-- The defect of the logarithmic modulus from a constant is harmonic wherever
the holomorphic function is nonzero. -/
theorem harmonicOnNhd_logarithmic_defect {f : ℂ → ℂ} {U : Set ℂ} (M : ℝ)
    (hf : AnalyticOnNhd ℂ f U) (hzero : ∀ z ∈ U, f z ≠ 0) :
    HarmonicOnNhd (fun z => Real.log M - Real.log ‖f z‖) U := by
  intro z hz
  exact (harmonicAt_const (Real.log M)).sub ((hf z hz).harmonicAt_log_norm (hzero z hz))

/-- A zero-free holomorphic function cannot be too small on an inner disk
relative to one value there and an outer boundary bound. -/
theorem norm_ge_exp_logarithmic_defect {f : ℂ → ℂ} {c v w : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : ∀ z ∈ closedBall c R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (hv : v ∈ closedBall c r) (hw : w ∈ closedBall c r) :
    M * Real.exp (-((R + r) / (R - r)) ^ 2 * Real.log (M / ‖f v‖)) ≤ ‖f w‖ := by
  have hvR : v ∈ closedBall c R := (closedBall_subset_closedBall hrR.le) hv
  have hwR : w ∈ closedBall c R := (closedBall_subset_closedBall hrR.le) hw
  have hvpos : 0 < ‖f v‖ := norm_pos_iff.mpr (hzero v hvR)
  have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hzero w hwR)
  have h := harmonic_harnack_two_points_inner_disk hr hrR
    (harmonicOnNhd_logarithmic_defect M hf hzero) hv hw
    (fun z hz => sub_nonneg.mpr (Real.log_le_log
      (norm_pos_iff.mpr (hzero z (sphere_subset_closedBall hz))) (hbound z hz)))
  have hlog : Real.log (M / ‖f v‖) = Real.log M - Real.log ‖f v‖ :=
    Real.log_div hM.ne' hvpos.ne'
  have he : Real.log M - ((R + r) / (R - r)) ^ 2 * Real.log (M / ‖f v‖) ≤
      Real.log ‖f w‖ := by rw [hlog]; linarith
  have hexp := Real.exp_le_exp.mpr he
  rw [Real.exp_sub, Real.exp_log hM, Real.exp_log hwpos] at hexp
  simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using hexp

/-- A zero-free function on the open radius-two disk has a quantitative
lower bound throughout the closed unit disk. The auxiliary Poisson circle has
radius `3/2`, so all nonvanishing hypotheses are strictly inside the domain. -/
theorem norm_ge_of_zero_free_logarithmic_growth {f : ℂ → ℂ} {c v w : ℂ} {M S : ℝ}
    (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c 2))
    (hzero : ∀ z ∈ ball c 2, f z ≠ 0)
    (hbound : ∀ z ∈ ball c 2, ‖f z‖ ≤ M)
    (hv : v ∈ closedBall c 1) (hw : w ∈ closedBall c 1)
    (hgrowth : Real.log (M / ‖f v‖) ≤ S) :
    M * Real.exp (-25 * S) ≤ ‖f w‖ := by
  have hsub : closedBall c (3 / 2 : ℝ) ⊆ ball c 2 :=
    closedBall_subset_ball (by norm_num)
  have h := norm_ge_exp_logarithmic_defect (r := 1) (R := 3 / 2)
    (by norm_num) (by norm_num) hM (hf.mono hsub)
    (fun z hz => hzero z (hsub hz))
    (fun z hz => hbound z (hsub (sphere_subset_closedBall hz))) hv hw
  norm_num at h
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM.le).trans h
  linarith

/-- Relative growth from the unit disk gives a uniform modulus lower bound
for a holomorphic function that is zero-free on the open radius-two disk. -/
theorem norm_ge_diskNorm_of_zero_free_logarithmic_growth {f : ℂ → ℂ} {c w : ℂ} {M S : ℝ}
    (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c 2))
    (hzero : ∀ z ∈ ball c 2, f z ≠ 0)
    (hbound : ∀ z ∈ ball c 2, ‖f z‖ ≤ M)
    (hw : w ∈ closedBall c 1)
    (hgrowth : Real.log (M / diskNorm f c 1) ≤ S) :
    diskNorm f c 1 * Real.exp (-25 * S) ≤ ‖f w‖ := by
  have hsub : closedBall c (1 : ℝ) ⊆ ball c 2 := closedBall_subset_ball (by norm_num)
  have hfsmall : ContinuousOn f (closedBall c 1) := hf.continuousOn.mono hsub
  obtain ⟨v, hv, _, hmax⟩ := exists_max_norm_in_closedBall hfsmall
    ⟨c, mem_closedBall_self (by norm_num), hzero c (mem_ball_self (by norm_num))⟩
  have heq : diskNorm f c 1 = ‖f v‖ := diskNorm_eq_of_isMax hv hmax
  have h := norm_ge_of_zero_free_logarithmic_growth hM hf hzero hbound hv hw
    (by simpa only [heq] using hgrowth)
  exact (mul_le_mul_of_nonneg_right (by rw [heq]; exact hbound v (hsub hv))
    (Real.exp_pos _).le).trans h

end Erdos522

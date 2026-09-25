/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HolomorphicLowerBound
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Logarithmic derivatives of zero-free holomorphic functions

A primitive of `f'/f` supplies a normalized analytic logarithm on a disk.
Borel–Carathéodory and Schwarz then bound its derivative linearly in the
logarithmic modulus defect. Harnack transfers that defect from a specified
anchor to the points where the derivative is estimated.
-/

noncomputable section
open Complex InnerProductSpace Metric Real Set
namespace Erdos522

/-- A zero-free holomorphic function on a disk has a normalized analytic
logarithm, constructed as a primitive of its logarithmic derivative. -/
theorem exists_normalized_analytic_logarithm {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball c R))
    (hzero : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball c R) ∧ F c = 0 ∧
      (∀ z ∈ ball c R, HasDerivAt F (deriv f z / f z) z) ∧
      (∀ z ∈ ball c R, Complex.exp (F z) = f z / f c) := by
  have hg : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    hf.deriv.differentiableOn.div hf.differentiableOn hzero
  obtain ⟨F, hFc, hF⟩ := hg.isExactOn_ball.with_val_at c 0
  have hFa : AnalyticOnNhd ℂ F (ball c R) :=
    (show DifferentiableOn ℂ F (ball c R) from
      fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  let g : ℂ → ℂ := fun z => Complex.exp (-F z) * f z
  have hgder (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt g 0 z := by
    have h := ((hF z hz).neg.cexp).mul (hf z hz).differentiableAt.hasDerivAt
    convert h using 1
    field_simp [hzero z hz]
    ring
  have hconst (z : ℂ) (hz : z ∈ ball c R) : g z = f c := by
    have h := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hgder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hgder z hz).deriv) hz (mem_ball_self hR)
    simpa [g, hFc] using h
  refine ⟨F, hFa, hFc, hF, fun z hz => ?_⟩
  have h := hconst z hz
  dsimp [g] at h
  rw [Complex.exp_neg] at h
  have h' := congrArg (fun t : ℂ => Complex.exp (F z) * t) h
  simp only [← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul] at h'
  exact (eq_div_iff (hzero c (mem_ball_self hR))).mpr h'.symm

/-- The real part of a normalized analytic logarithm is its logarithmic
modulus ratio. -/
theorem real_part_normalized_logarithm {f F : ℂ → ℂ} {c z : ℂ}
    (hc : f c ≠ 0) (hz : f z ≠ 0) (hF : Complex.exp (F z) = f z / f c) :
    (F z).re = Real.log ‖f z‖ - Real.log ‖f c‖ := by
  have h := congrArg norm hF
  rw [Complex.norm_exp, norm_div] at h
  have hl := congrArg Real.log h
  rw [Real.log_exp, Real.log_div (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hc)] at hl
  exact hl

/-- A real-part upper bound controls the central derivative of a holomorphic
function vanishing at the center. -/
theorem norm_deriv_le_four_mul_div_of_re_bound_pos {F : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hF : AnalyticOnNhd ℂ F (ball c R))
    (hFc : F c = 0) (hbound : ∀ z ∈ ball c R, (F z).re ≤ B) :
    ‖deriv F c‖ ≤ 4 * B / R := by
  let G : ℂ → ℂ := fun z => F (c + z)
  have hG : DifferentiableOn ℂ G (ball 0 R) := by
    apply hF.differentiableOn.comp (by fun_prop)
    intro z hz
    simpa [dist_eq_norm] using hz
  have hGbound : MapsTo G (ball 0 R) {z | z.re ≤ B} := by
    intro z hz
    apply hbound
    simpa [dist_eq_norm] using hz
  have hG0 : G 0 = 0 := by simpa [G] using hFc
  have hmaps : MapsTo F (ball c (R / 2)) (closedBall (F c) (2 * B)) := by
    intro z hz
    have hd : ‖z - c‖ < R / 2 := mem_ball_iff_norm.mp hz
    have hzR : z - c ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      linarith
    have h := borelCaratheodory_zero hB hG hGbound hR hzR hG0
    have hGz : G (z - c) = F z := by simp [G]
    rw [hGz] at h
    rw [mem_closedBall_iff_norm, hFc, sub_zero]
    refine h.trans ?_
    apply (div_le_iff₀ (by linarith : 0 < R - ‖z - c‖)).mpr
    nlinarith
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball
    (hF.differentiableOn.mono (ball_subset_ball (by linarith))) hmaps (by positivity)
  convert h using 1
  ring

/-- The central derivative estimate also includes a zero real-part bound. -/
theorem norm_deriv_le_four_mul_div_of_re_bound {F : ℂ → ℂ} {c : ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hF : AnalyticOnNhd ℂ F (ball c R))
    (hFc : F c = 0) (hbound : ∀ z ∈ ball c R, (F z).re ≤ B) :
    ‖deriv F c‖ ≤ 4 * B / R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hB' : 0 < B + ε * R / 4 := by positivity
  have h := norm_deriv_le_four_mul_div_of_re_bound_pos hR hB' hF hFc
    (fun z hz => (hbound z hz).trans (le_add_of_nonneg_right (by positivity)))
  have heq : 4 * (B + ε * R / 4) / R = 4 * B / R + ε := by
    field_simp
  rwa [heq] at h

/-- A zero-free holomorphic function bounded by `M` has logarithmic derivative
at the center controlled linearly by its logarithmic modulus defect. -/
theorem norm_logarithmicDerivative_le_center {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c R))
    (hzero : ∀ z ∈ ball c R, f z ≠ 0)
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ M) :
    ‖deriv f c / f c‖ ≤ 4 * Real.log (M / ‖f c‖) / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hzero c hc)
  obtain ⟨F, hFa, hFc, hFder, hFexp⟩ := exists_normalized_analytic_logarithm hR hf hzero
  have hlog : Real.log (M / ‖f c‖) = Real.log M - Real.log ‖f c‖ :=
    Real.log_div hM.ne' hfc.ne'
  have hnonneg : 0 ≤ Real.log (M / ‖f c‖) := by
    rw [hlog]
    exact sub_nonneg.mpr (Real.log_le_log hfc (hbound c hc))
  have hreal (z : ℂ) (hz : z ∈ ball c R) : (F z).re ≤ Real.log (M / ‖f c‖) := by
    rw [real_part_normalized_logarithm (hzero c hc) (hzero z hz) (hFexp z hz), hlog]
    exact sub_le_sub_right
      (Real.log_le_log (norm_pos_iff.mpr (hzero z hz)) (hbound z hz)) _
  have h := norm_deriv_le_four_mul_div_of_re_bound hR hnonneg hFa hFc hreal
  rwa [(hFder c hc).deriv] at h

/-- On a radius-`r` disk, logarithmic growth from an anchor controls the
logarithmic derivative by `200 S/r`. The function is zero-free on the open
radius-`2r` disk. -/
theorem norm_logarithmicDerivative_le_inner_disk {f : ℂ → ℂ} {c v w : ℂ} {r M S : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c (2 * r)))
    (hzero : ∀ z ∈ ball c (2 * r), f z ≠ 0)
    (hbound : ∀ z ∈ ball c (2 * r), ‖f z‖ ≤ M)
    (hv : v ∈ closedBall c r) (hw : w ∈ closedBall c r)
    (hgrowth : Real.log (M / ‖f v‖) ≤ S) :
    ‖deriv f w / f w‖ ≤ 200 * S / r := by
  have hsub : closedBall c (3 * r / 2) ⊆ ball c (2 * r) :=
    closedBall_subset_ball (by linarith)
  have hunit : closedBall c r ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  have hvpos : 0 < ‖f v‖ := norm_pos_iff.mpr (hzero v (hunit hv))
  have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hzero w (hunit hw))
  have hdef := harmonic_harnack_two_points_inner_disk hr.le (show r < 3 * r / 2 by linarith)
    (harmonicOnNhd_logarithmic_defect M (hf.mono hsub) (fun z hz => hzero z (hsub hz)))
    hv hw (fun z hz => sub_nonneg.mpr (Real.log_le_log
      (norm_pos_iff.mpr (hzero z (hsub (sphere_subset_closedBall hz))))
      (hbound z (hsub (sphere_subset_closedBall hz)))))
  have hratio : ((3 * r / 2 + r) / (3 * r / 2 - r)) ^ 2 = (25 : ℝ) := by
    field_simp
    ring
  rw [hratio] at hdef
  have hlogv : Real.log (M / ‖f v‖) = Real.log M - Real.log ‖f v‖ :=
    Real.log_div hM.ne' hvpos.ne'
  have hlogw : Real.log (M / ‖f w‖) = Real.log M - Real.log ‖f w‖ :=
    Real.log_div hM.ne' hwpos.ne'
  have hdefect : Real.log (M / ‖f w‖) ≤ 25 * S := by
    rw [hlogv] at hgrowth
    rw [hlogw]
    linarith
  have hlocal : ball w (r / 2) ⊆ ball c (2 * r) := by
    apply ball_subset_ball'
    have := mem_closedBall.mp hw
    linarith
  have h := norm_logarithmicDerivative_le_center (by positivity : 0 < r / 2) hM
    (hf.mono hlocal) (fun z hz => hzero z (hlocal hz))
    (fun z hz => hbound z (hlocal hz))
  refine h.trans ?_
  apply (div_le_div_iff₀ (show 0 < r / 2 by positivity) hr).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdefect hr.le]

/-- Logarithmic growth relative to the inner disk maximum controls the
logarithmic derivative throughout that closed disk. -/
theorem norm_logarithmicDerivative_le_of_disk_growth {f : ℂ → ℂ} {c w : ℂ} {r M S : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c (2 * r)))
    (hzero : ∀ z ∈ ball c (2 * r), f z ≠ 0)
    (hbound : ∀ z ∈ ball c (2 * r), ‖f z‖ ≤ M)
    (hw : w ∈ closedBall c r)
    (hgrowth : Real.log (M / diskNorm f c r) ≤ S) :
    ‖deriv f w / f w‖ ≤ 200 * S / r := by
  have hsub : closedBall c r ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  have hfsmall : ContinuousOn f (closedBall c r) := hf.continuousOn.mono hsub
  obtain ⟨v, hv, _, hmax⟩ := exists_max_norm_in_closedBall hfsmall
    ⟨c, mem_closedBall_self hr.le, hzero c (mem_ball_self (by positivity))⟩
  have heq : diskNorm f c r = ‖f v‖ := diskNorm_eq_of_isMax hv hmax
  exact norm_logarithmicDerivative_le_inner_disk hr hM hf hzero hbound hv hw
    (by simpa only [heq] using hgrowth)

/-- The disk-growth estimate in the native logarithmic-derivative notation. -/
theorem norm_logDeriv_le_of_disk_growth {f : ℂ → ℂ} {c w : ℂ} {r M S : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hf : AnalyticOnNhd ℂ f (ball c (2 * r)))
    (hzero : ∀ z ∈ ball c (2 * r), f z ≠ 0)
    (hbound : ∀ z ∈ ball c (2 * r), ‖f z‖ ≤ M)
    (hw : w ∈ closedBall c r)
    (hgrowth : Real.log (M / diskNorm f c r) ≤ S) :
    ‖logDeriv f w‖ ≤ 200 * S / r :=
  norm_logarithmicDerivative_le_of_disk_growth hr hM hf hzero hbound hw hgrowth

end Erdos522

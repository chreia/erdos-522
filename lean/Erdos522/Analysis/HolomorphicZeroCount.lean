/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Order.Compact

/-!
# Holomorphic growth and multiplicity-counted zeros

Jensen's inequality bounds the zero divisor using any nonzero center value.
Choosing a point of maximum modulus on an inner disk makes the resulting
bound depend only on the growth between concentric disks.
-/

noncomputable section
open Filter MeromorphicOn Metric Set Topology
namespace Erdos522

/-- The sum of an analytic zero divisor increases with the compact domain. -/
theorem sum_divisor_le_of_subset {f : ℂ → ℂ} {U V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hU : IsCompact U) (hV : IsCompact V) (hUV : U ⊆ V) :
    (∑ᶠ z, divisor f U z) ≤ ∑ᶠ z, divisor f V z := by
  apply finsum_le_finsum ((divisor f U).finiteSupport hU) ((divisor f V).finiteSupport hV)
  intro z
  by_cases hz : z ∈ U
  · rw [(hf.mono hUV).divisor_apply hz, hf.divisor_apply (hUV hz)]
  · rw [(divisor f U).apply_eq_zero_of_notMem hz]
    exact hf.divisor_nonneg z

/-- Jensen's zero-count bound with an arbitrary positive supremum bound.
Scaling the function reduces the outer bound to one without changing its divisor. -/
theorem sum_divisor_le_log_ratio {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  let g : ℂ → ℂ := (M : ℂ)⁻¹ • f
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := hf.const_smul
  have hgnorm (z : ℂ) : ‖g z‖ = ‖f z‖ / M := by
    simp only [g, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    ring
  have hgc : g c ≠ 0 := by
    change (M : ℂ)⁻¹ * f c ≠ 0
    exact mul_ne_zero (inv_ne_zero hM') hc
  have hgbound : ∀ z ∈ sphere c R, ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hgnorm]
    exact (div_le_one hM).mpr (hbound z hz)
  have hj := AnalyticOnNhd.sum_divisor_le
    (r := r) (R := R) (M := 1)
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR)
    (by norm_num) (by simpa only [abs_of_pos (hr.trans hrR)] using hg) hgc
    (by simpa only [abs_of_pos (hr.trans hrR)] using hgbound)
  rw [abs_of_pos hr, hgnorm, one_div_div] at hj
  simpa only [g, divisor_const_smul (inv_ne_zero hM')] using hj

/-- A nonzero entire function has a nonzero value in every disk of positive radius. -/
theorem exists_ne_zero_in_closedBall {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ closedBall c r, f z ≠ 0 := by
  by_contra! h
  have hevent : f =ᶠ[𝓝 c] (0 : ℂ → ℂ) := by
    filter_upwards [Metric.ball_mem_nhds c hr] with z hz
    exact h z (ball_subset_closedBall hz)
  exact hne (hf.eq_of_eventuallyEq analyticOnNhd_const hevent)

/-- Every zero of a nonzero entire function has finite analytic order. -/
theorem analyticOrderAt_ne_top_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  exact hne (hf.eq_of_eventuallyEq analyticOnNhd_const (analyticOrderAt_eq_top.mp htop))

/-- On its domain, the divisor of a nonzero entire function records its natural
order of vanishing at every point. -/
theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : f ≠ 0) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [(hf.mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_entire hf hne z)]
  simp

/-- An inner-disk maximum supplies a nonzero value for recentered Jensen estimates. -/
theorem exists_max_norm_in_closedBall {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : ContinuousOn f (closedBall c r))
    (hne : ∃ z ∈ closedBall c r, f z ≠ 0) :
    ∃ u ∈ closedBall c r, f u ≠ 0 ∧ ∀ z ∈ closedBall c r, ‖f z‖ ≤ ‖f u‖ := by
  obtain ⟨z, hz, hz0⟩ := hne
  obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall c r).exists_isMaxOn ⟨z, hz⟩ hf.norm
  refine ⟨u, hu, ?_, hmax⟩
  exact norm_pos_iff.mp ((norm_pos_iff.mpr hz0).trans_le (hmax hz))

/-- The supremum of the modulus on a closed disk. -/
def diskNorm (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' closedBall c r)

/-- A point of maximum modulus realizes the closed-disk norm. -/
theorem diskNorm_eq_of_isMax {f : ℂ → ℂ} {c u : ℂ} {r : ℝ}
    (hu : u ∈ closedBall c r) (hmax : ∀ z ∈ closedBall c r, ‖f z‖ ≤ ‖f u‖) :
    diskNorm f c r = ‖f u‖ := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨u, hu, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hmax z hz

/-- Continuity bounds every disk value by its disk norm. -/
theorem norm_le_diskNorm {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ diskNorm f c r := by
  exact le_csSup ((isCompact_closedBall c r).image_of_continuousOn hf.norm).bddAbove
    ⟨z, hz, rfl⟩

/-- Recentered Jensen controls the zeros of an inner disk by a nonzero value
in that disk and a norm bound on the disk of four times the radius. -/
theorem sum_divisor_le_of_recentered_growth {f : ℂ → ℂ} {c u : ℂ} {r A : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall c (4 * r)))
    (hu : u ∈ closedBall c r) (hfu : f u ≠ 0)
    (hbound : ∀ z ∈ closedBall c (4 * r), ‖f z‖ ≤ A * ‖f u‖) :
    ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
      Real.log A / Real.log ((3 : ℝ) / 2) := by
  have houter : closedBall u (3 * r) ⊆ closedBall c (4 * r) := by
    intro z hz
    have htri := dist_triangle z u c
    have hz' := mem_closedBall.mp hz
    have hu' := mem_closedBall.mp hu
    apply mem_closedBall.mpr
    linarith
  have hinner : closedBall c r ⊆ closedBall u (2 * r) := by
    intro z hz
    have htri := dist_triangle z c u
    have hz' := mem_closedBall.mp hz
    have hu' : dist c u ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hu
    apply mem_closedBall.mpr
    linarith
  have hlocal := hf.mono houter
  have hcount : (∑ᶠ z, divisor f (closedBall c r) z) ≤
      ∑ᶠ z, divisor f (closedBall u (2 * r)) z :=
    sum_divisor_le_of_subset
      (hlocal.mono (closedBall_subset_closedBall (by linarith : 2 * r ≤ 3 * r)))
      (isCompact_closedBall ..) (isCompact_closedBall ..) hinner
  have hj := sum_divisor_le_log_ratio (r := 2 * r) (R := 3 * r)
    (by linarith) (by linarith) (mul_pos hA (norm_pos_iff.mpr hfu)) hlocal hfu
    (fun z hz => hbound z (houter (sphere_subset_closedBall hz)))
  have hradius : (3 * r) / (2 * r) = (3 : ℝ) / 2 := by field_simp
  rw [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hfu), hradius] at hj
  exact (show ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    ((∑ᶠ z, divisor f (closedBall u (2 * r)) z : ℤ) : ℝ) by exact_mod_cast hcount).trans hj

/-- Growth between concentric disks bounds the full zero divisor, including
multiplicities and zeros on the inner boundary. -/
theorem sum_divisor_le_of_disk_growth {f : ℂ → ℂ} {c : ℂ} {r A : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hf : AnalyticOnNhd ℂ f (closedBall c (4 * r)))
    (hne : ∃ z ∈ closedBall c r, f z ≠ 0)
    (hgrowth : diskNorm f c (4 * r) ≤ A * diskNorm f c r) :
    ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
      Real.log A / Real.log ((3 : ℝ) / 2) := by
  have hsub : closedBall c r ⊆ closedBall c (4 * r) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨u, hu, hfu, hmax⟩ := exists_max_norm_in_closedBall (hf.continuousOn.mono hsub) hne
  apply sum_divisor_le_of_recentered_growth hr hA hf hu hfu
  intro z hz
  calc
    ‖f z‖ ≤ diskNorm f c (4 * r) := norm_le_diskNorm hf.continuousOn hz
    _ ≤ A * diskNorm f c r := hgrowth
    _ = A * ‖f u‖ := by rw [diskNorm_eq_of_isMax hu hmax]

end Erdos522

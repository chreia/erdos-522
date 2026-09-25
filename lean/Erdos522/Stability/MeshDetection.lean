/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.RootIsolation
import Erdos522.Probability.Covariance.JetEvaluation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Detecting small-derivative roots on a mesh

A quadratic Taylor estimate transfers a small derivative at a root to joint
small values of the polynomial and its radial derivative at a nearby mesh point.
The quantitative spacing is uniform throughout the prescribed annulus.
-/

noncomputable section
open Polynomial

namespace Erdos522

/-- Taylor's formula and the derivative mean-value theorem at a nearby root. -/
theorem nearby_root_value_derivative_bounds (P : Polynomial ℂ) {D : Set ℂ}
    {α z : ℂ} {M d h : ℝ} (hD : Convex ℝ D) (hαD : α ∈ D) (hzD : z ∈ D)
    (hM : 0 ≤ M) (hd : 0 ≤ d) (_hh : 0 ≤ h) (hroot : P.eval α = 0)
    (hderiv : ‖P.derivative.eval α‖ ≤ d) (hdist : ‖z - α‖ ≤ h)
    (hbound : ∀ w ∈ D, ‖P.derivative.derivative.eval w‖ ≤ M) :
    ‖P.eval z‖ ≤ d * h + M / 2 * h ^ 2 ∧
      ‖P.derivative.eval z‖ ≤ d + M * h := by
  have ht := polynomial_taylor_remainder P hD hαD hzD hbound
  rw [hroot, sub_zero] at ht
  have hv : ‖P.eval z‖ ≤ ‖P.eval z - P.derivative.eval α * (z - α)‖ +
      ‖P.derivative.eval α * (z - α)‖ := norm_le_norm_sub_add _ _
  have hlin : ‖P.derivative.eval α * (z - α)‖ ≤ d * h := by
    rw [norm_mul]
    exact mul_le_mul hderiv hdist (norm_nonneg _) hd
  have hquad : M / 2 * ‖z - α‖ ^ 2 ≤ M / 2 * h ^ 2 := by gcongr
  have hdifference := hD.norm_image_sub_le_of_norm_deriv_le
    (fun w _ => P.derivative.differentiableAt)
    (fun w hw => by simpa only [Polynomial.deriv] using hbound w hw) hαD hzD
  have htri := norm_le_norm_sub_add (P.derivative.eval z) (P.derivative.eval α)
  constructor
  · linarith
  · have hdiff : ‖P.derivative.eval z - P.derivative.eval α‖ ≤ M * h :=
      hdifference.trans (mul_le_mul_of_nonneg_left hdist hM)
    linarith

/-- The radial-angular mesh spacing at derivative scale `L`. -/
def derivativeMeshSpacing (N : ℕ) (S L : ℝ) : ℝ :=
  1 / (64 * S * N * L * Real.sqrt (Real.log N))

/-- The value threshold detected by the derivative mesh. -/
def derivativeMeshValueThreshold (N : ℕ) (S L : ℝ) : ℝ :=
  1 / (16 * S * L ^ 2 * Real.sqrt (Real.log N))

/-- At every degree at least two, the logarithmic square root exceeds one half. -/
theorem half_le_sqrt_log {N : ℕ} (hN : 2 ≤ N) :
    (1 / 2 : ℝ) ≤ Real.sqrt (Real.log N) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  apply Real.le_sqrt_of_sq_le
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2
  linarith [Real.log_two_gt_d9]

/-- The mesh spacing stays within the radial padding `1/N`. -/
theorem derivativeMeshSpacing_le_inv_degree {N : ℕ} (hN : 2 ≤ N)
    {S L : ℝ} (hS : 1 ≤ S) (hL : 1 ≤ L) :
    0 < derivativeMeshSpacing N S L ∧ derivativeMeshSpacing N S L ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrt := half_le_sqrt_log hN
  have hden : (N : ℝ) ≤ 64 * S * N * L * Real.sqrt (Real.log N) := by
    have hp : (1 : ℝ) ≤ S * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hL)]
    have hq : (1 : ℝ) ≤ 64 * S * L * Real.sqrt (Real.log N) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hN0.le
    nlinarith
  unfold derivativeMeshSpacing
  constructor
  · positivity
  · exact one_div_le_one_div_of_le hN0 hden

/-- The small mesh displacement remains inside the annulus's enlarged disk. -/
theorem derivative_mesh_point_in_disk {N : ℕ} (hN : 2 ≤ N) {K S L : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) {α z : ℂ}
    (hα : |‖α‖ - 1| ≤ K / N) (hz : ‖z - α‖ ≤ derivativeMeshSpacing N S L) :
    ‖z‖ ≤ 1 + (K + 1) / N := by
  have hαupper := (abs_le.mp hα).2
  have hmesh := (derivativeMeshSpacing_le_inv_degree hN hS hL).2
  have hnorm := norm_le_norm_sub_add z α
  have heq : (K + 1) / (N : ℝ) = K / N + 1 / N := by ring
  rw [heq]
  linarith

/-- A small-derivative annular root produces the exact joint small-value test at every nearby mesh point. -/
theorem annular_root_mesh_detection (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K S L : ℝ} (_hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hKN : K + 1 ≤ (N : ℝ))
    {α z : ℂ} (hα : |‖α‖ - 1| ≤ K / N) (hroot : P.eval α = 0)
    (hderiv : ‖P.derivative.eval α‖ ≤ (N : ℝ) * Real.sqrt N / L)
    (hz : ‖z - α‖ ≤ derivativeMeshSpacing N S L)
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ 2 * Real.sqrt N * Real.sqrt (Real.log N)) :
    ‖P.eval z‖ / Real.sqrt N ≤ derivativeMeshValueThreshold N S L ∧
      ‖z * P.derivative.eval z‖ / ((N : ℝ) * Real.sqrt N) ≤ 3 / L := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hS0 : 0 < S := by linarith
  have hL0 : 0 < L := by linarith
  have hnroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hlogroot : 0 < Real.sqrt (Real.log N) := by linarith [half_le_sqrt_log hN]
  have hh := derivativeMeshSpacing_le_inv_degree hN hS hL
  have hzD := derivative_mesh_point_in_disk hN hS hL hα hz
  have hαD : ‖α‖ ≤ 1 + (K + 1) / N := by
    have := (abs_le.mp hα).2
    have hfrac : K / (N : ℝ) ≤ (K + 1) / N := div_le_div_of_nonneg_right (by linarith) hN0.le
    linarith
  have hz2 : ‖z‖ ≤ 2 := by
    have := (div_le_one₀ hN0).mpr hKN
    linarith
  have hbasic := nearby_root_value_derivative_bounds P (convex_closedBall (0 : ℂ) (1 + (K + 1) / N))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hαD)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hzD)
    (by positivity) (by positivity) hh.1.le hroot hderiv hz
    (fun w hw => hbound w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have hMh : (S * (N : ℝ) ^ 2 * Real.sqrt N * Real.sqrt (Real.log N)) *
      derivativeMeshSpacing N S L = ((N : ℝ) * Real.sqrt N / L) / 64 := by
    unfold derivativeMeshSpacing
    field_simp
  have hvalue : ‖P.eval z‖ ≤ 2 * ((N : ℝ) * Real.sqrt N / L) * derivativeMeshSpacing N S L := by
    have hMhh := congrArg (fun x : ℝ => x * derivativeMeshSpacing N S L) hMh
    have hd : 0 ≤ (N : ℝ) * Real.sqrt N / L := by positivity
    nlinarith [mul_nonneg hd hh.1.le]
  have hderivz : ‖P.derivative.eval z‖ ≤
      ((N : ℝ) * Real.sqrt N / L) + ((N : ℝ) * Real.sqrt N / L) / 64 := by
    simpa only [hMh] using hbasic.2
  constructor
  · apply (div_le_div_of_nonneg_right hvalue hnroot.le).trans
    have heq : (2 * ((N : ℝ) * Real.sqrt N / L) * derivativeMeshSpacing N S L) / Real.sqrt N =
        derivativeMeshValueThreshold N S L / 2 := by
      unfold derivativeMeshSpacing derivativeMeshValueThreshold
      field_simp
      ring
    rw [heq]
    have hu : 0 ≤ derivativeMeshValueThreshold N S L := by unfold derivativeMeshValueThreshold; positivity
    linarith
  · rw [norm_mul]
    have hprod : ‖z‖ * ‖P.derivative.eval z‖ ≤ 3 * ((N : ℝ) * Real.sqrt N / L) := by
      have hpre := mul_le_mul hz2 hderivz (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
      have hd : 0 ≤ (N : ℝ) * Real.sqrt N / L := by positivity
      nlinarith
    apply (div_le_div_of_nonneg_right hprod (by positivity)).trans
    have heq : (3 * ((N : ℝ) * Real.sqrt N / L)) / ((N : ℝ) * Real.sqrt N) = 3 / L := by field_simp
    exact heq.le

/-- The natural second-derivative scale equals its real-power normalization. -/
theorem degree_sq_mul_sqrt_eq_five_halves (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ 2 * Real.sqrt N = (N : ℝ) ^ (5 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ = (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
      norm_num [Real.sqrt_eq_rpow]
    _ = (N : ℝ) ^ (2 + 1 / 2 : ℝ) := (Real.rpow_add hn _ _).symm
    _ = _ := by norm_num

/-- Mesh detection with the real powers used for polynomial jets. -/
theorem annular_root_mesh_detection_rpow (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K S L : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hKN : K + 1 ≤ (N : ℝ))
    {α z : ℂ} (hα : |‖α‖ - 1| ≤ K / N) (hroot : P.eval α = 0)
    (hderiv : ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L)
    (hz : ‖z - α‖ ≤ derivativeMeshSpacing N S L)
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N)) :
    ‖P.eval z‖ / Real.sqrt N ≤ derivativeMeshValueThreshold N S L ∧
      ‖z * P.derivative.eval z‖ / (N : ℝ) ^ (3 / 2 : ℝ) ≤ 3 / L := by
  have hNp : 0 < N := by omega
  have hd : ‖P.derivative.eval α‖ ≤ (N : ℝ) * Real.sqrt N / L := by
    simpa only [degree_mul_sqrt_eq_three_halves N hNp] using hderiv
  have hb (w : ℂ) (hw : ‖w‖ ≤ 1 + (K + 1) / N) :
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ 2 * Real.sqrt N * Real.sqrt (Real.log N) := by
    rw [mul_assoc S, degree_sq_mul_sqrt_eq_five_halves N hNp]
    exact hbound w hw
  simpa only [degree_mul_sqrt_eq_three_halves N hNp] using
    annular_root_mesh_detection P hN hK hS hL hKN hα hroot hd hz hb

/-- The angular distance to the real axis is half the norm of the doubled angle. -/
def realAxisAngularDistance (θ : Real.Angle) : ℝ := ‖(2 : ℕ) • θ‖ / 2

/-- Angular distance to the real axis changes by at most the angular displacement. -/
theorem realAxisAngularDistance_le_add_dist (θ φ : Real.Angle) :
    realAxisAngularDistance θ ≤ realAxisAngularDistance φ + dist θ φ := by
  have ht := norm_le_norm_sub_add ((2 : ℕ) • θ) ((2 : ℕ) • φ)
  have hdouble : ‖(2 : ℕ) • θ - (2 : ℕ) • φ‖ ≤ 2 * dist θ φ := by
    rw [← nsmul_sub, dist_eq_norm]
    exact norm_nsmul_le
  unfold realAxisAngularDistance
  linarith

/-- Enlarging the excluded real sectors by one mesh displacement preserves retained angles. -/
theorem real_sector_retention {θ φ : Real.Angle} {t : ℝ}
    (hθ : 2 * t ≤ realAxisAngularDistance θ) (hnear : dist θ φ ≤ t) :
    t ≤ realAxisAngularDistance φ := by
  linarith [realAxisAngularDistance_le_add_dist θ φ]

/-- At the prescribed mesh spacing, a root outside the doubled sectors has a retained angle. -/
theorem derivative_mesh_sector_retention {N : ℕ} (hN : 2 ≤ N) {S L : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) {θ φ : Real.Angle}
    (hθ : 2 / Real.sqrt N ≤ realAxisAngularDistance θ)
    (hnear : dist θ φ ≤ derivativeMeshSpacing N S L) :
    1 / Real.sqrt N ≤ realAxisAngularDistance φ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  apply real_sector_retention (by simpa only [mul_one_div] using hθ)
  apply hnear.trans ((derivativeMeshSpacing_le_inv_degree hN hS hL).2.trans _)
  exact one_div_le_one_div_of_le hsqrt
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (by omega : 1 ≤ N))))

end Erdos522

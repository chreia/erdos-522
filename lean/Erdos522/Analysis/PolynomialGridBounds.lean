/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LocalZeroCount
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundary grids for polynomial suprema

A derivative envelope controls interpolation between boundary samples. The
maximum modulus principle then supplies the same estimate on the closed disk.
-/

noncomputable section
open Polynomial

namespace Erdos522

/-- Equally spaced boundary points on a circle of radius `R`. -/
def polynomialBoundaryGrid (R : ℝ) (J : ℕ) (i : Fin J) : ℂ :=
  (R : ℂ) * (AddCircle.toCircle (LocalZeroCount.angularGrid J i) : ℂ)

@[simp] theorem norm_polynomialBoundaryGrid (R : ℝ) (J : ℕ) (i : Fin J) :
    ‖polynomialBoundaryGrid R J i‖ = |R| := by
  simp [polynomialBoundaryGrid]

/-- The boundary grid is a geometric net with explicit chord radius. -/
theorem exists_near_polynomialBoundaryGrid {R : ℝ} (hR : 0 < R) {J : ℕ} (hJ : 0 < J)
    {z : ℂ} (hz : ‖z‖ = R) :
    ∃ i : Fin J, ‖z - polynomialBoundaryGrid R J i‖ ≤ 2 * Real.pi * R / J := by
  let u : Circle := ⟨z / (R : ℂ), by
    change z / (R : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    simp only [Metric.mem_sphere, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR, hz, div_self hR.ne']⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective u
  rw [AddCircle.homeomorphCircle_apply] at hθ
  have hθc : (AddCircle.toCircle θ : ℂ) = z / (R : ℂ) := congrArg Subtype.val hθ
  have hzθ : z = (R : ℂ) * (AddCircle.toCircle θ : ℂ) := by
    rw [hθc, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
  obtain ⟨i, hi⟩ := LocalZeroCount.exists_near_angularGrid hJ θ
  refine ⟨i, ?_⟩
  rw [hzθ, polynomialBoundaryGrid, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  calc
    _ ≤ R * (2 * Real.pi * dist θ (LocalZeroCount.angularGrid J i)) :=
      mul_le_mul_of_nonneg_left (LocalZeroCount.circle_chord_le_angular_distance _ _) hR.le
    _ ≤ R * (2 * Real.pi * (1 / (J : ℝ))) := by gcongr
    _ = _ := by ring

/-- Derivative bounds control polynomial increments within a disk. -/
theorem polynomial_norm_sub_le_of_derivative_bound (P : Polynomial ℂ) {R M : ℝ}
    (hderiv : ∀ z, ‖z‖ ≤ R → ‖P.derivative.eval z‖ ≤ M)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖P.eval z - P.eval w‖ ≤ M * ‖z - w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Metric.closedBall (0 : ℂ) R)
    (fun _ _ => P.differentiableAt)
  · intro x hx
    rw [P.deriv]
    exact hderiv x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · exact convex_closedBall (0 : ℂ) R
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- A boundary grid and a derivative envelope give a uniform bound on the closed disk. -/
theorem polynomial_disk_bound_of_boundary_grid (P : Polynomial ℂ) {R M t : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) {J : ℕ} (hJ : 0 < J)
    (hderiv : ∀ z, ‖z‖ ≤ R → ‖P.derivative.eval z‖ ≤ M)
    (hgrid : ∀ i : Fin J, ‖P.eval (polynomialBoundaryGrid R J i)‖ ≤ t)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖P.eval z‖ ≤ t + M * (2 * Real.pi * R / J) := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.ball (0 : ℂ) R) Metric.isBounded_ball P.differentiable.diffContOnCl
  · intro w hw
    have hwR : ‖w‖ = R := by
      simpa only [frontier_ball (0 : ℂ) hR.ne', Metric.mem_sphere, dist_zero_right] using hw
    obtain ⟨i, hi⟩ := exists_near_polynomialBoundaryGrid hR hJ hwR
    have hig : ‖polynomialBoundaryGrid R J i‖ ≤ R := by simp [abs_of_pos hR]
    have hd := polynomial_norm_sub_le_of_derivative_bound P hderiv hwR.le hig
    calc
      ‖P.eval w‖ ≤ ‖P.eval w - P.eval (polynomialBoundaryGrid R J i)‖ +
          ‖P.eval (polynomialBoundaryGrid R J i)‖ := norm_le_norm_sub_add _ _
      _ ≤ M * ‖w - polynomialBoundaryGrid R J i‖ + t := add_le_add hd (hgrid i)
      _ ≤ t + M * (2 * Real.pi * R / J) := by nlinarith
  · simpa only [closure_ball (0 : ℂ) hR.ne', Metric.mem_closedBall, dist_zero_right] using hz

end Erdos522

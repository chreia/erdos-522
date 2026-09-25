/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Radial projection of polynomial factors

Projecting roots onto the unit circle controls the product of their distances
from a point on the circle. A single normalization value absorbs the leading
coefficient and the radial factors.
-/

noncomputable section

open scoped BigOperators

namespace Erdos522

/-- A radial factor controls the distance between two unit vectors. -/
theorem unit_sphere_radial_distance_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z u : E} (hz : ‖z‖ = 1) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) * ‖z - u‖ ≤ 2 * ‖z - r • u‖ := by
  have hd : ‖z - u‖ ≤ 2 := by
    simpa only [hz, hu, one_add_one_eq_two] using norm_sub_le z u
  have hi : ‖z - r • u‖ ^ 2 = (1 - r) ^ 2 + r * ‖z - u‖ ^ 2 := by
    simp only [norm_sub_sq_real, hz, hu, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, real_inner_smul_right]
    ring
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg _)) (by positivity)).mp
  have hsq : ‖z - u‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (z - u)]
  have hp := mul_nonneg (sq_nonneg (1 - r)) (sub_nonneg.mpr hsq)
  nlinarith

/-- A normalization value controls the leading coefficient times the radial envelope. -/
theorem radial_product_envelope_ge_one {ι : Type*} [Fintype ι]
    (c : ℂ) (u : ι → ℂ) (r : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1)
    (hr : ∀ i, 0 ≤ r i) {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (hnorm : 1 ≤ ‖c * ∏ i, (z₀ - (r i : ℂ) * u i)‖) :
    1 ≤ ‖c‖ * ∏ i, (1 + r i) := by
  refine hnorm.trans ?_
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  calc
    ‖z₀ - (r i : ℂ) * u i‖ ≤ ‖z₀‖ + ‖(r i : ℂ) * u i‖ := norm_sub_le _ _
    _ = 1 + r i := by simp [hz₀, hu, Complex.norm_real, abs_of_nonneg (hr i)]

/-- Radially projecting all roots costs at most `2^degree` on the unit circle.
    The radii may vanish; multiplicities are retained in the indexed product. -/
theorem norm_projected_product_le {ι : Type*} [Fintype ι]
    (c : ℂ) (u : ι → ℂ) (r : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1)
    (hr : ∀ i, 0 ≤ r i) {z₀ z : ℂ} (hz₀ : ‖z₀‖ = 1) (hz : ‖z‖ = 1)
    (hnorm : 1 ≤ ‖c * ∏ i, (z₀ - (r i : ℂ) * u i)‖) :
    ‖∏ i, (z - u i)‖ ≤ (2 : ℝ) ^ Fintype.card ι *
      ‖c * ∏ i, (z - (r i : ℂ) * u i)‖ := by
  have henv := radial_product_envelope_ge_one c u r hu hr hz₀ hnorm
  have hprod : (∏ i, (1 + r i)) * (∏ i, ‖z - u i‖) ≤
      (2 : ℝ) ^ Fintype.card ι * ∏ i, ‖z - (r i : ℂ) * u i‖ := by
    have htwo : (2 : ℝ) ^ Fintype.card ι = ∏ _i : ι, (2 : ℝ) := by simp
    rw [← Finset.prod_mul_distrib, htwo, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (add_nonneg zero_le_one (hr i)) (norm_nonneg _))
    intro i _
    exact unit_sphere_radial_distance_bound hz (hu i) (hr i)
  simp only [norm_mul, norm_prod]
  calc
    _ ≤ (‖c‖ * ∏ i, (1 + r i)) * ∏ i, ‖z - u i‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right henv
        (Finset.prod_nonneg (fun i _ => norm_nonneg (z - u i)))
    _ = ‖c‖ * ((∏ i, (1 + r i)) * ∏ i, ‖z - u i‖) := by ring
    _ ≤ ‖c‖ * ((2 : ℝ) ^ Fintype.card ι * ∏ i, ‖z - (r i : ℂ) * u i‖) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg c)
    _ = _ := by ring

end Erdos522

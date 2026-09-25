/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.RightEndpointSums
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Power-weighted exponential sums

Right-endpoint approximation gives the limiting integral even when the
weight has an integrable singularity at zero. The exponential parameter may
vary with the mesh, as it does for polynomial radii `1+x/N`.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Erdos522

/-- Sampling from above uniformly controls both positive and negative powers. -/
theorem rpow_rightEndpointSample_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (a : ℝ) :
    rightEndpointSample N x ^ a ≤ 1 + x ^ a := by
  have hy := rightEndpointSample_mem hN ⟨hx.1.le, hx.2⟩
  by_cases ha : 0 ≤ a
  · exact (Real.rpow_le_one hy.1.le hy.2 ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.1.le a))
  · have hxy := (rightEndpointSample_bounds hN hx.1.le).1.le
    exact (Real.rpow_le_rpow_of_nonpos hx.1 hxy (le_of_not_ge ha)).trans
      (le_add_of_nonneg_left (by norm_num))

/-- Power-weighted exponential Riemann sums converge for every integrable
power and every convergent real exponential parameter. -/
theorem tendsto_powerWeighted_exponential_sum {a b : ℝ} (ha : -1 < a)
    (bN : ℕ → ℝ) (hb : Tendsto bN atTop (𝓝 b)) :
    Tendsto (fun N : ℕ => (∑ j : Fin N,
      (((j.val : ℝ) + 1) / N) ^ a * Real.exp (2 * bN N * (((j.val : ℝ) + 1) / N))) / N)
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, t ^ a * Real.exp (2 * b * t))) := by
  let B : ℝ := Real.exp (2 * (|b| + 1))
  apply tendsto_rightEndpointSums_of_dominated
    (fun N t => t ^ a * Real.exp (2 * bN N * t))
    (fun t => t ^ a * Real.exp (2 * b * t)) (fun t => B * (1 + t ^ a))
  · have hp : IntegrableOn (fun t : ℝ => t ^ a) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr ha
    exact ((integrable_const (1 : ℝ)).add hp).const_mul B
  · filter_upwards [eventually_ge_atTop 1,
      hb.abs.eventually_lt_const (show |b| < |b| + 1 by linarith)] with N hN hbN
    intro t ht
    have hNpos : 0 < N := by omega
    have hy := rightEndpointSample_mem hNpos ⟨ht.1.le, ht.2⟩
    have he : 2 * bN N * rightEndpointSample N t ≤ 2 * (|b| + 1) := by
      have h₁ := mul_le_mul_of_nonneg_right (le_abs_self (bN N)) hy.1.le
      have h₂ := mul_le_mul_of_nonneg_left hy.2 (abs_nonneg (bN N))
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hy.1.le _) (Real.exp_nonneg _))]
    calc
      _ ≤ (1 + t ^ a) * B := mul_le_mul
        (rpow_rightEndpointSample_le hNpos ht a) (Real.exp_le_exp.mpr he)
        (Real.exp_nonneg _) (by linarith [Real.rpow_nonneg ht.1.le a])
      _ = _ := by ring
  · intro t ht
    have hs := tendsto_rightEndpointSample ht.1.le
    exact (hs.rpow_const (Or.inl ht.1.ne')).mul
      (Real.continuous_exp.continuousAt.tendsto.comp ((hb.const_mul 2).mul hs))

end Erdos522

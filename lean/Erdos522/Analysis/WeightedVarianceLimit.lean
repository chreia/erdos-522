/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PowerWeightedSums
import Erdos522.Analysis.WeightedProfileDerivative
import Erdos522.Analysis.KacVarianceProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The limiting variance of power-weighted Kac polynomials

The constant coefficient is one and the coefficient at degree `k≥1` has
size `k^τ`. After division by `N^(2τ+1)`, the variance is a right-endpoint
sum with exponential parameter `N log(1+x/N)`, plus a vanishing constant term.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Erdos522

/-- Variance for power weights with constant coefficient one. -/
def weightedRadialVariance (τ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  1 + ∑ j : Fin N, ((j.val : ℝ) + 1) ^ (2 * τ) * r ^ (2 * (j.val + 1))

theorem weightedRadialVariance_pos (τ : ℝ) (N : ℕ) (r : ℝ) :
    0 < weightedRadialVariance τ N r := by
  have hs : 0 ≤ ∑ j : Fin N, ((j.val : ℝ) + 1) ^ (2 * τ) * r ^ (2 * (j.val + 1)) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by rw [pow_mul]; positivity)
  unfold weightedRadialVariance
  linarith

/-- Exponential form of a radial monomial at a sampled degree. -/
theorem exp_scaled_log_radius {N k : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    Real.exp (2 * ((N : ℝ) * Real.log r) * ((k : ℝ) / N)) = r ^ (2 * k) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : 2 * ((N : ℝ) * Real.log r) * ((k : ℝ) / N) = ((2 * k : ℕ) : ℝ) * Real.log r := by
    push_cast
    field_simp
  rw [he, Real.exp_nat_mul, Real.exp_log hr]

/-- Exact conversion of the finite radial variance to a weighted Riemann sum. -/
theorem weightedRadialVariance_normalized_eq (τ : ℝ) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) :
    weightedRadialVariance τ N r / (N : ℝ) ^ (2 * τ + 1) =
      (N : ℝ) ^ (-(2 * τ + 1)) +
        (∑ j : Fin N, (((j.val : ℝ) + 1) / N) ^ (2 * τ) *
          Real.exp (2 * ((N : ℝ) * Real.log r) * (((j.val : ℝ) + 1) / N))) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (j : Fin N) :
      (((j.val : ℝ) + 1) / N) ^ (2 * τ) *
        Real.exp (2 * ((N : ℝ) * Real.log r) * (((j.val : ℝ) + 1) / N)) =
      (((j.val : ℝ) + 1) ^ (2 * τ) * r ^ (2 * (j.val + 1))) / (N : ℝ) ^ (2 * τ) := by
    have he := exp_scaled_log_radius (k := j.val + 1) hN hr
    push_cast at he
    rw [he, Real.div_rpow (by positivity) hn.le]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, weightedRadialVariance, Real.rpow_add hn,
    Real.rpow_one, Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
  field_simp

/-- The normalized power-weighted variance converges at every scaled radius. -/
theorem tendsto_weightedRadialVariance_profile (τ x : ℝ) (hτ : -(1 / 2 : ℝ) < τ) :
    Tendsto (fun N : ℕ => weightedRadialVariance τ N (1 + x / N) /
      (N : ℝ) ^ (2 * τ + 1)) atTop (𝓝 (weightedVarianceProfile τ x)) := by
  have ht := tendsto_powerWeighted_exponential_sum (by linarith : -1 < 2 * τ)
    (fun N : ℕ => (N : ℝ) * Real.log (1 + x / N)) (tendsto_degree_mul_log_kac_radius x)
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(2 * τ + 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum := hz.add ht
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_kac_radius x).eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with N hN hr
  exact (weightedRadialVariance_normalized_eq τ (by omega) hr).symm

end Erdos522

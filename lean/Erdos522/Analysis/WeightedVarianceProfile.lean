/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.WeightedVarianceLimit
import Erdos522.Analysis.MonotoneProfileLimits

/-!
# Compact-uniform limits of weighted variance profiles

The finite variance and its logarithmic normalization converge uniformly on
compact sets of scaled radii.  Monotonicity upgrades pointwise convergence;
truncating negative radii at zero supplies globally monotone approximants
which agree with the original radii eventually on each compact set.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace Erdos522

/-- Standard deviation for power-weighted coefficients. -/
def weightedRadialSigma (τ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (weightedRadialVariance τ N r)

theorem weightedRadialSigma_pos (τ : ℝ) (N : ℕ) (r : ℝ) :
    0 < weightedRadialSigma τ N r :=
  Real.sqrt_pos.mpr (weightedRadialVariance_pos τ N r)

/-- The weighted variance increases with a nonnegative radius. -/
theorem weightedRadialVariance_mono {τ r s : ℝ} (N : ℕ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    weightedRadialVariance τ N r ≤ weightedRadialVariance τ N s := by
  unfold weightedRadialVariance
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _)
    (Real.rpow_nonneg (by positivity) _)

/-- On a compact scaled interval, the original radius is eventually nonnegative. -/
theorem eventually_nonneg_scaled_radius_on_compact {s : Set ℝ} (hs : IsCompact s) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ s, 0 ≤ 1 + x / N := by
  obtain ⟨a, ha⟩ := hs.bddBelow
  have hN : ∀ᶠ N : ℕ in atTop, max 1 (-a) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max 1 (-a)))
  filter_upwards [hN] with N hN
  intro x hx
  have hn : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hN)
  have hxN : -(N : ℝ) ≤ x := by linarith [ha hx, (le_max_right 1 (-a)).trans hN]
  have hh : -1 ≤ x / N := (le_div_iff₀ hn).mpr (by linarith)
  linarith

private theorem monotone_nonnegative_scaled_radius (N : ℕ) :
    Monotone (fun x : ℝ => max 0 (1 + x / N)) := by
  intro x y hxy
  exact max_le_max_left _ (add_le_add le_rfl
    (div_le_div_of_nonneg_right hxy (Nat.cast_nonneg N)))

/-- Pointwise logarithmic normalization with its precise power of the degree. -/
theorem tendsto_log_weightedRadialSigma_profile (τ x : ℝ) (hτ : -1 / 2 < τ) :
    Tendsto (fun N : ℕ => Real.log (weightedRadialSigma τ N (1 + x / N)) -
      (τ + 1 / 2) * Real.log N) atTop (𝓝 (weightedLogVarianceProfile τ x)) := by
  have ht := ((tendsto_weightedRadialVariance_profile τ x (by linarith)).log
    (weightedVarianceProfile_pos hτ x).ne').const_mul (1 / 2 : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.log_div (weightedRadialVariance_pos τ N _).ne' (Real.rpow_pos_of_pos hn _).ne',
    Real.log_rpow hn, weightedRadialSigma,
    Real.log_sqrt (weightedRadialVariance_pos τ N _).le]
  ring

/-- The weighted finite variance converges uniformly on every compact set of scaled radii. -/
theorem weightedRadialVariance_profile_compact_uniform (τ : ℝ) (hτ : -1 / 2 < τ)
    {s : Set ℝ} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => weightedRadialVariance τ N (1 + x / N) /
        (N : ℝ) ^ (2 * τ + 1)) (weightedVarianceProfile τ) atTop s := by
  let f : ℕ → ℝ → ℝ := fun N x =>
    weightedRadialVariance τ N (max 0 (1 + x / N)) / (N : ℝ) ^ (2 * τ + 1)
  have hmono : ∀ N, Monotone (f N) := by
    intro N x y hxy
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    exact weightedRadialVariance_mono N (le_max_left _ _)
      (monotone_nonnegative_scaled_radius N hxy)
  have hpoint : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (weightedVarianceProfile τ x)) := by
    intro x
    apply (tendsto_weightedRadialVariance_profile τ x (by linarith)).congr'
    filter_upwards [(tendsto_kac_radius x).eventually_const_lt (by norm_num : (0 : ℝ) < 1)]
      with N hN
    simp only [f, max_eq_right hN.le]
  have hu := tendstoUniformlyOn_of_monotone_pointwise f (weightedVarianceProfile τ)
    hmono (continuous_weightedVarianceProfile hτ) hpoint hs
  apply hu.congr
  filter_upwards [eventually_nonneg_scaled_radius_on_compact hs] with N hN
  intro x hx
  simp only [f, max_eq_right (hN x hx)]

/-- The logarithm of the weighted standard deviation has the same compact-uniform normalization. -/
theorem log_weightedRadialSigma_profile_compact_uniform (τ : ℝ) (hτ : -1 / 2 < τ)
    {s : Set ℝ} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => Real.log (weightedRadialSigma τ N (1 + x / N)) -
        (τ + 1 / 2) * Real.log N) (weightedLogVarianceProfile τ) atTop s := by
  let f : ℕ → ℝ → ℝ := fun N x =>
    Real.log (weightedRadialSigma τ N (max 0 (1 + x / N))) - (τ + 1 / 2) * Real.log N
  have hmono : ∀ N, Monotone (f N) := by
    intro N x y hxy
    apply sub_le_sub_right
    apply Real.log_le_log (weightedRadialSigma_pos τ N _)
    exact Real.sqrt_le_sqrt (weightedRadialVariance_mono N (le_max_left _ _)
      (monotone_nonnegative_scaled_radius N hxy))
  have hpoint : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (weightedLogVarianceProfile τ x)) := by
    intro x
    apply (tendsto_log_weightedRadialSigma_profile τ x hτ).congr'
    filter_upwards [(tendsto_kac_radius x).eventually_const_lt (by norm_num : (0 : ℝ) < 1)]
      with N hN
    simp only [f, max_eq_right hN.le]
  have hu := tendstoUniformlyOn_of_monotone_pointwise f (weightedLogVarianceProfile τ)
    hmono (continuous_weightedLogVarianceProfile hτ) hpoint hs
  apply hu.congr
  filter_upwards [eventually_nonneg_scaled_radius_on_compact hs] with N hN
  intro x hx
  simp only [f, max_eq_right (hN x hx)]

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HolomorphicZeroCount
import Erdos522.Analysis.ComplexExponentialPropagation

/-!
# Zero counts for exponential polynomials

Concentric-disk propagation and recentered Jensen give coefficient-uniform
bounds for the zero divisor of a nonzero exponential polynomial. The bound
records both the spectral radius and the logarithmic dependence on the number
of terms introduced by discrete propagation.
-/

noncomputable section
open MeromorphicOn Metric Set
namespace Erdos522

/-- A finite exponential polynomial is entire. -/
theorem analyticOnNhd_complexExponentialSum {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ) :
    AnalyticOnNhd ℂ (complexExponentialSum s c ζ) univ := by
  intro z _
  unfold complexExponentialSum
  fun_prop

/-- A nonzero exponential polynomial has a nonzero value on every positive-radius disk. -/
theorem complexExponentialSum_ne_zero_in_closedBall {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (hne : complexExponentialSum s c ζ ≠ 0)
    (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ closedBall z₀ r, complexExponentialSum s c ζ z ≠ 0 :=
  exists_ne_zero_in_closedBall (analyticOnNhd_complexExponentialSum s c ζ) hne z₀ hr

/-- Jensen's bound for all zeros in a closed disk. The number of terms enters
as `(m - 1) log(32m)`, including when exponents coincide or coefficients vanish. -/
theorem sum_divisor_complexExponentialSum_le {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0)
    {σ r : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) (hr : 0 < r) (z₀ : ℂ) :
    ((∑ᶠ z, divisor (complexExponentialSum s c ζ) (closedBall z₀ r) z : ℤ) : ℝ) ≤
      (4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * (s.card : ℝ))) /
        Real.log ((3 : ℝ) / 2) := by
  let f := complexExponentialSum s c ζ
  let A : ℝ := Real.exp (4 * σ * r) * (32 * (s.card : ℝ)) ^ (s.card - 1)
  have hn : 1 ≤ s.card := Finset.one_le_card.mpr hs
  have hnR : (0 : ℝ) < s.card := by exact_mod_cast (by omega : 0 < s.card)
  have hA : 0 < A := by dsimp [A]; positivity
  have hf := analyticOnNhd_complexExponentialSum s c ζ
  have hfsmall : ContinuousOn f (closedBall z₀ r) := hf.continuousOn.mono (subset_univ _)
  obtain ⟨u, hu, hfu, hmax⟩ := exists_max_norm_in_closedBall hfsmall
    (complexExponentialSum_ne_zero_in_closedBall s c ζ hne z₀ hr)
  have hbound : ∀ z ∈ closedBall z₀ (4 * r), ‖f z‖ ≤ A * ‖f u‖ := by
    intro z hz
    have h := norm_complexExponentialSum_le_of_disk s hs c ζ hσ hζ hr
      (show r ≤ 4 * r by linarith) (norm_nonneg (f u)) z₀ z
      (fun w hw => hmax w hw) hz
    have hratio : 8 * (s.card : ℝ) * (4 * r) / r = 32 * (s.card : ℝ) := by
      field_simp
      ring
    rw [hratio] at h
    have hexp : σ * (4 * r) = 4 * σ * r := by ring
    rw [hexp] at h
    dsimp [A]
    nlinarith
  have hj := sum_divisor_le_of_recentered_growth hr hA
    (hf.mono (subset_univ _)) hu hfu hbound
  have hlog : Real.log A =
      4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * (s.card : ℝ)) := by
    dsimp [A]
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by positivity)),
      Real.log_exp, Real.log_pow, Nat.cast_sub hn, Nat.cast_one]
  rw [hlog] at hj
  exact hj

/-- A version of the exponential zero-count bound using only numerical coefficients. -/
theorem sum_divisor_complexExponentialSum_le_explicit {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (c ζ : ι → ℂ)
    (hne : complexExponentialSum s c ζ ≠ 0)
    {σ r : ℝ} (hσ : 0 ≤ σ) (hζ : ∀ j ∈ s, ‖ζ j‖ ≤ σ) (hr : 0 < r) (z₀ : ℂ) :
    ((∑ᶠ z, divisor (complexExponentialSum s c ζ) (closedBall z₀ r) z : ℤ) : ℝ) ≤
      12 * σ * r + 3 * ((s.card : ℝ) - 1) * Real.log (32 * (s.card : ℝ)) := by
  have hn : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.one_le_card.mpr hs
  have hlog : (1 : ℝ) / 3 ≤ Real.log ((3 : ℝ) / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogpos : 0 < Real.log ((3 : ℝ) / 2) := by linarith
  have hnonneg : 0 ≤ 4 * σ * r + ((s.card : ℝ) - 1) * Real.log (32 * (s.card : ℝ)) := by
    apply add_nonneg (by positivity)
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  refine (sum_divisor_complexExponentialSum_le s hs c ζ hne hσ hζ hr z₀).trans ?_
  apply (div_le_iff₀ hlogpos).mpr
  nlinarith

end Erdos522

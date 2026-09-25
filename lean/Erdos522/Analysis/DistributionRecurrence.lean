/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Finite distribution recurrences

A negative power of the set measure is a potential for the iterative
restricted-energy estimate. Its decrease controls the accumulated logarithmic
loss along every finite chain.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522

/-- The measure increment in the distribution recurrence. -/
def distributionStep (p c μ : ℝ) : ℝ := c / p ^ 2 * μ ^ (1 + 1 / p)

/-- In the probability range, one increment is at most the current measure. -/
theorem distributionStep_le {p c μ : ℝ} (hp : 1 ≤ p) (hc1 : c ≤ 1)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) : distributionStep p c μ ≤ μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hcdiv : c / p ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hp0)).mpr (hc1.trans hp2)
  have hpow : μ ^ (1 / p) ≤ 1 := Real.rpow_le_one hμ.le hμ1 (by positivity)
  unfold distributionStep
  rw [Real.rpow_add hμ, Real.rpow_one]
  calc
    _ = μ * ((c / p ^ 2) * μ ^ (1 / p)) := by ring
    _ ≤ μ * (1 * 1) := by gcongr
    _ = μ := by ring

/-- The reciprocal-power potential decreases by a definite amount at every step.
    The proof integrates the derivative on an interval contained in `[μ, 2μ]`. -/
theorem reciprocal_power_drop {p c μ : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    c / (4 * p ^ 3) * μ ^ (-(1 / p)) ≤
      μ ^ (-(2 / p)) - (μ + distributionStep p c μ) ^ (-(2 / p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let h : ℝ := distributionStep p c μ
  let q : ℝ := -(2 / p) - 1
  have hh : 0 < h := by dsimp [h, distributionStep]; positivity
  have hupper : μ + h ≤ 2 * μ := by
    have hs := distributionStep_le hp hc1 hμ hμ1
    dsimp [h]
    linarith
  have hab : μ ≤ μ + h := by linarith
  have hq0 : q ≤ 0 := by
    have hi : 0 < 2 / p := by positivity
    dsimp [q]
    linarith
  have hq3 : -3 ≤ q := by
    have hi : 2 / p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
    dsimp [q]
    linarith
  have htwo : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ q := by
    calc
      (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq3
  have hcont : ContinuousOn (fun x : ℝ => (2 / p) * x ^ q) (Set.uIcc μ (μ + h)) := by
    apply continuousOn_const.mul
    apply continuousOn_id.rpow_const
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact Or.inl (ne_of_gt (hμ.trans_le hx.1))
  have hint := hcont.intervalIntegrable (μ := volume)
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc μ (μ + h)) :
      HasDerivAt (fun y : ℝ => -(y ^ (-(2 / p)))) ((2 / p) * x ^ q) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hμ.trans_le hx.1)
    convert (Real.hasDerivAt_rpow_const (p := -(2 / p)) (Or.inl hx0)).neg using 1
    dsimp [q]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc μ (μ + h)) :
      (1 / (4 * p)) * μ ^ q ≤ (2 / p) * x ^ q := by
    have hx0 : 0 < x := hμ.trans_le hx.1
    have hx2 : x ≤ 2 * μ := hx.2.trans hupper
    have hpow := Real.rpow_le_rpow_of_nonpos hx0 hx2 hq0
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hμ.le] at hpow
    calc
      _ = (2 / p) * ((1 / 8) * μ ^ q) := by ring
      _ ≤ (2 / p) * ((2 : ℝ) ^ q * μ ^ q) := by gcongr
      _ ≤ (2 / p) * x ^ q := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hscale : (μ + h - μ) * ((1 / (4 * p)) * μ ^ q) =
      c / (4 * p ^ 3) * μ ^ (-(1 / p)) := by
    dsimp [h, distributionStep]
    calc
      _ = c / (4 * p ^ 3) * (μ ^ (1 + 1 / p) * μ ^ q) := by field_simp; ring
      _ = _ := by
        rw [← Real.rpow_add hμ]
        congr 2
        dsimp [q]
        ring
  rw [hscale, hftc] at hbound
  simpa only [neg_sub_neg] using hbound

/-- Along a finite increasing-measure chain, the reciprocal first powers have
    a summable bound given by the initial reciprocal-square potential. -/
theorem sum_reciprocal_power_le {p c : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (μ : ℕ → ℝ) (M : ℕ)
    (hμ : ∀ k ≤ M, 0 < μ k ∧ μ k ≤ 1)
    (hstep : ∀ k < M, μ (k + 1) = μ k + distributionStep p c (μ k)) :
    (∑ k ∈ Finset.range M, (μ k) ^ (-(1 / p))) ≤
      (4 * p ^ 3 / c) * (μ 0) ^ (-(2 / p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hcoef : 0 < c / (4 * p ^ 3) := by positivity
  have hsum : (c / (4 * p ^ 3)) *
      (∑ k ∈ Finset.range M, (μ k) ^ (-(1 / p))) ≤
      ∑ k ∈ Finset.range M, ((μ k) ^ (-(2 / p)) - (μ (k + 1)) ^ (-(2 / p))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkM := Finset.mem_range.mp hk
    rw [hstep k hkM]
    exact reciprocal_power_drop hp hc hc1 (hμ k hkM.le).1 (hμ k hkM.le).2
  rw [Finset.sum_range_sub'] at hsum
  have hlast : 0 ≤ (μ M) ^ (-(2 / p)) := Real.rpow_nonneg (hμ M le_rfl).1.le _
  have hbound : (∑ k ∈ Finset.range M, (μ k) ^ (-(1 / p))) ≤
      (μ 0) ^ (-(2 / p)) / (c / (4 * p ^ 3)) := by
    apply (le_div_iff₀ hcoef).mpr
    nlinarith
  apply hbound.trans_eq
  field_simp

/-- A finite chain of per-step logarithmic losses telescopes to an explicit
    fifth-power cost in the moment parameter. -/
theorem sum_distribution_losses_le {p c C : ℝ} (hp : 1 ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C) (μ loss : ℕ → ℝ) (M : ℕ)
    (hμ : ∀ k ≤ M, 0 < μ k ∧ μ k ≤ 1)
    (hstep : ∀ k < M, μ (k + 1) = μ k + distributionStep p c (μ k))
    (hloss : ∀ k < M,
      loss k ≤ C * p ^ 2 * (μ k) ^ (-(1 / p)) * Real.log (p / μ 0)) :
    (∑ k ∈ Finset.range M, loss k) ≤
      (4 * C / c) * p ^ 5 * (μ 0) ^ (-(2 / p)) * Real.log (p / μ 0) := by
  have hlog : 0 ≤ Real.log (p / μ 0) := by
    apply Real.log_nonneg
    exact (one_le_div (hμ 0 (Nat.zero_le M)).1).mpr ((hμ 0 (Nat.zero_le M)).2.trans hp)
  calc
    _ ≤ ∑ k ∈ Finset.range M, C * p ^ 2 * (μ k) ^ (-(1 / p)) * Real.log (p / μ 0) :=
      Finset.sum_le_sum (fun k hk => hloss k (Finset.mem_range.mp hk))
    _ = (C * p ^ 2 * Real.log (p / μ 0)) *
        (∑ k ∈ Finset.range M, (μ k) ^ (-(1 / p))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (C * p ^ 2 * Real.log (p / μ 0)) *
        ((4 * p ^ 3 / c) * (μ 0) ^ (-(2 / p))) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_power_le hp hc hc1 μ M hμ hstep)
        (by positivity)
    _ = _ := by ring

/-- An integer moment order adapted to the initial measure. -/
def distributionMomentOrder (μ : ℝ) : ℕ := ⌈2 * Real.log (2 / μ)⌉₊

/-- The selected moment order lies between twice and four times the logarithmic scale. -/
theorem distributionMomentOrder_bounds {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    1 ≤ distributionMomentOrder μ ∧
      2 * Real.log (2 / μ) ≤ (distributionMomentOrder μ : ℝ) ∧
      (distributionMomentOrder μ : ℝ) ≤ 4 * Real.log (2 / μ) := by
  have hratio : (2 : ℝ) ≤ 2 / μ := (le_div_iff₀ hμ).mpr (by linarith)
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 / μ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
    nlinarith [Real.log_two_gt_d9]
  have hlo : 2 * Real.log (2 / μ) ≤ (distributionMomentOrder μ : ℝ) := Nat.le_ceil _
  have hhi : (distributionMomentOrder μ : ℝ) < 2 * Real.log (2 / μ) + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  refine ⟨?_, hlo, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ (distributionMomentOrder μ : ℝ) by linarith)
  · linarith

/-- At the logarithmically chosen order, the reciprocal-power factor is at most `exp(1)`. -/
theorem distributionMomentOrder_reciprocal_power_le {μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    μ ^ (-(2 / (distributionMomentOrder μ : ℝ))) ≤ Real.exp 1 := by
  obtain ⟨hp, hlow, _⟩ := distributionMomentOrder_bounds hμ hμ1
  have hp0 : (0 : ℝ) < distributionMomentOrder μ := by exact_mod_cast (by omega)
  rw [Real.rpow_def_of_pos hμ]
  apply Real.exp_le_exp.mpr
  rw [show Real.log μ * (-(2 / (distributionMomentOrder μ : ℝ))) =
      (-2 * Real.log μ) / (distributionMomentOrder μ : ℝ) by ring]
  apply (div_le_iff₀ hp0).mpr
  rw [Real.log_div (by norm_num) hμ.ne'] at hlow
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The finite recurrence cost has the sixth-power logarithmic scale. -/
theorem optimized_distribution_cost_le {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (distributionMomentOrder μ : ℝ) ^ 5 *
        μ ^ (-(2 / (distributionMomentOrder μ : ℝ))) *
        Real.log ((distributionMomentOrder μ : ℝ) / μ) ≤
      5120 * Real.exp 1 * (Real.log (2 / μ)) ^ 6 := by
  obtain ⟨hp, hlo, hhi⟩ := distributionMomentOrder_bounds hμ hμ1
  have hp0 : (0 : ℝ) < distributionMomentOrder μ := by exact_mod_cast (by omega)
  have hL : 0 ≤ Real.log (2 / μ) := by
    apply Real.log_nonneg
    exact (one_le_div hμ).mpr (by linarith)
  have hlog : Real.log ((distributionMomentOrder μ : ℝ) / μ) ≤
      5 * Real.log (2 / μ) := by
    rw [Real.log_div hp0.ne' hμ.ne']
    have hpLog := Real.log_le_self hp0.le
    have hminus : -Real.log μ ≤ Real.log (2 / μ) := by
      rw [Real.log_div (by norm_num) hμ.ne']
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    linarith
  have hlog0 : 0 ≤ Real.log ((distributionMomentOrder μ : ℝ) / μ) := by
    apply Real.log_nonneg
    exact (one_le_div hμ).mpr (hμ1.trans (by exact_mod_cast hp))
  have hpow := distributionMomentOrder_reciprocal_power_le hμ hμ1
  calc
    _ ≤ (4 * Real.log (2 / μ)) ^ 5 * Real.exp 1 * (5 * Real.log (2 / μ)) := by gcongr
    _ = _ := by ring

/-- A finite logarithmic-loss chain, with the moment order optimized at its initial measure. -/
theorem sum_distribution_losses_le_log_six {c C : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C) (μ loss : ℕ → ℝ) (M : ℕ)
    (hμ : ∀ k ≤ M, 0 < μ k ∧ μ k ≤ 1)
    (hstep : ∀ k < M, μ (k + 1) = μ k +
      distributionStep (distributionMomentOrder (μ 0) : ℝ) c (μ k))
    (hloss : ∀ k < M, loss k ≤ C * (distributionMomentOrder (μ 0) : ℝ) ^ 2 *
      (μ k) ^ (-(1 / (distributionMomentOrder (μ 0) : ℝ))) *
      Real.log ((distributionMomentOrder (μ 0) : ℝ) / μ 0)) :
    (∑ k ∈ Finset.range M, loss k) ≤
      (20480 * Real.exp 1 * C / c) * (Real.log (2 / μ 0)) ^ 6 := by
  have hμ0 := hμ 0 (Nat.zero_le M)
  have hp : (1 : ℝ) ≤ distributionMomentOrder (μ 0) := by
    exact_mod_cast (distributionMomentOrder_bounds hμ0.1 hμ0.2).1
  have h := sum_distribution_losses_le hp hc hc1 hC μ loss M hμ hstep hloss
  calc
    _ ≤ (4 * C / c) * (distributionMomentOrder (μ 0) : ℝ) ^ 5 *
        (μ 0) ^ (-(2 / (distributionMomentOrder (μ 0) : ℝ))) *
        Real.log ((distributionMomentOrder (μ 0) : ℝ) / μ 0) := h
    _ = (4 * C / c) * ((distributionMomentOrder (μ 0) : ℝ) ^ 5 *
        (μ 0) ^ (-(2 / (distributionMomentOrder (μ 0) : ℝ))) *
        Real.log ((distributionMomentOrder (μ 0) : ℝ) / μ 0)) := by ring
    _ ≤ (4 * C / c) * (5120 * Real.exp 1 * (Real.log (2 / μ 0)) ^ 6) :=
      mul_le_mul_of_nonneg_left (optimized_distribution_cost_le hμ0.1 hμ0.2) (by positivity)
    _ = _ := by ring

/-- Finite one-step inequalities sum to an endpoint estimate. -/
theorem initial_le_terminal_add_sum (value loss : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ k < M, value k ≤ value (k + 1) + loss k) :
    value 0 ≤ value M + ∑ k ∈ Finset.range M, loss k := by
  have hsum : (∑ k ∈ Finset.range M, (value k - value (k + 1))) ≤
      ∑ k ∈ Finset.range M, loss k := by
    apply Finset.sum_le_sum
    intro k hk
    have h := hstep k (Finset.mem_range.mp hk)
    linarith
  rw [Finset.sum_range_sub'] at hsum
  linarith

/-- A finite logarithmic recurrence has an explicit sixth-power endpoint bound. -/
theorem finite_distribution_recurrence_bound {c C : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C) (μ value : ℕ → ℝ) (M : ℕ)
    (hμ : ∀ k ≤ M, 0 < μ k ∧ μ k ≤ 1)
    (hstep : ∀ k < M, μ (k + 1) = μ k +
      distributionStep (distributionMomentOrder (μ 0) : ℝ) c (μ k))
    (hvalue : ∀ k < M, value k ≤ value (k + 1) +
      C * (distributionMomentOrder (μ 0) : ℝ) ^ 2 *
        (μ k) ^ (-(1 / (distributionMomentOrder (μ 0) : ℝ))) *
        Real.log ((distributionMomentOrder (μ 0) : ℝ) / μ 0)) :
    value 0 ≤ value M +
      (20480 * Real.exp 1 * C / c) * (Real.log (2 / μ 0)) ^ 6 := by
  let loss (k : ℕ) : ℝ := C * (distributionMomentOrder (μ 0) : ℝ) ^ 2 *
    (μ k) ^ (-(1 / (distributionMomentOrder (μ 0) : ℝ))) *
      Real.log ((distributionMomentOrder (μ 0) : ℝ) / μ 0)
  have hsum := sum_distribution_losses_le_log_six hc hc1 hC μ loss M hμ hstep
    (fun _ _ => le_rfl)
  have htel := initial_le_terminal_add_sum value loss M hvalue
  linarith

end Erdos522

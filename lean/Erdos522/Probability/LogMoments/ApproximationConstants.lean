/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.RestrictedApproximation
import Erdos522.Probability.LogMoments.PropagationOrder

/-!
# Quantitative bounds for exponential approximation

The finite spectral and local approximation constants have logarithmic cost
proportional to the approximation order. Substituting the restricted-energy
shift order makes its dependence on the moment order and event mass explicit.
-/

noncomputable section
namespace Erdos522.LogMoments

/-- The reciprocal spectral cutoff in polynomial form. -/
theorem inv_spectralEnergyCutoff (n : ℕ) :
    1 / spectralEnergyCutoff n =
      2 * ((n : ℝ) + 1) ^ 2 * (256 * ((n : ℝ) + 1) ^ 4) ^ (2 * n) := by
  unfold spectralEnergyCutoff
  have heq : (1 / (128 * ((n : ℝ) + 1) ^ 4)) / 2 =
      1 / (256 * ((n : ℝ) + 1) ^ 4) := by
    rw [div_div]
    congr 1
    ring
  rw [heq, one_div_div, one_div_pow, div_eq_mul_inv, one_div, inv_inv]

/-- A single power controls every finite constant in the restricted-energy
approximation theorem. -/
theorem restrictedApproximationConstant_le {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    restrictedApproximationConstant n δ ≤
      (256 * ((n : ℝ) + 1) / δ) ^ (32 * n) := by
  let x : ℝ := (n : ℝ) + 1
  let B : ℝ := 256 * x / δ
  have hx : 1 ≤ x := by dsimp [x]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : 0 ≤ x := by linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : 256 * x ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hBx : x ≤ B := by nlinarith
  have hB1 : 1 ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by nlinarith
  have hB256 : 256 ≤ B := by nlinarith
  have hpi : 6 * Real.pi ≤ B := by linarith [Real.pi_lt_four]
  have hsmall : 8 * x / δ ≤ B := by dsimp [B]; gcongr; norm_num
  have hcutbase : 256 * x ^ 4 ≤ B ^ 5 := by
    calc
      _ ≤ B * B ^ 4 := by gcongr
      _ = _ := by ring
  have hcutpref : 2 * x ^ 2 ≤ B ^ 3 := by
    calc
      _ ≤ B * B ^ 2 := by gcongr
      _ = _ := by ring
  have hcut : 1 / spectralEnergyCutoff n ≤ B ^ (10 * n + 3) := by
    rw [inv_spectralEnergyCutoff]
    change 2 * x ^ 2 * (256 * x ^ 4) ^ (2 * n) ≤ _
    calc
      _ ≤ B ^ 3 * (B ^ 5) ^ (2 * n) := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hlocalbase : 8 * x ^ 2 ≤ B ^ 3 := by
    calc
      _ ≤ B * B ^ 2 := by gcongr; linarith
      _ = _ := by ring
  have hlocal : 1 / (1 / (8 * x ^ 2)) ^ (2 * n) ≤ B ^ (10 * n + 3) := by
    rw [one_div_pow, one_div_one_div]
    calc
      _ ≤ (B ^ 3) ^ (2 * n) := by gcongr
      _ = B ^ (6 * n) := by rw [← pow_mul]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)
  have hsum : 1 / spectralEnergyCutoff n + 1 / (1 / (8 * x ^ 2)) ^ (2 * n) ≤
      B ^ (10 * n + 4) := by
    calc
      _ ≤ 2 * B ^ (10 * n + 3) := by linarith
      _ ≤ B * B ^ (10 * n + 3) := by gcongr
      _ = _ := by rw [← pow_succ']
  unfold restrictedApproximationConstant
  change x ^ 2 * (6 * Real.pi) ^ (2 * n) * (8 * x / δ) *
    (1 / spectralEnergyCutoff n + 1 / (1 / (8 * x ^ 2)) ^ (2 * n)) ≤ B ^ (32 * n)
  calc
    _ ≤ B ^ 2 * B ^ (2 * n) * B * B ^ (10 * n + 4) := by
      have := (spectralEnergyCutoff_pos n).le
      gcongr
    _ = B ^ (12 * n + 7) := by
      rw [← pow_add, ← pow_succ, ← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)

/-- Logarithmic cost of the approximation constant. -/
theorem log_restrictedApproximationConstant_le {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (restrictedApproximationConstant n δ) ≤
      32 * (n : ℝ) * Real.log (256 * ((n : ℝ) + 1) / δ) := by
  have h := Real.log_le_log (restrictedApproximationConstant_pos n hδ)
    (restrictedApproximationConstant_le hn hδ hδ1)
  simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using h

/-- An upper bound for the number of small shifts, including the ceiling. -/
theorem shiftOrder_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) :
    (shiftOrder δ p : ℝ) ≤
      4096 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hexp : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  have hD : 1 ≤ δ ^ (-(1 / (p : ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr (by positivity))
  have htwo : (2 : ℝ) ^ (1 / (p : ℝ)) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) (show 1 / (p : ℝ) ≤ 1 by
        apply (div_le_iff₀ hp0).mpr
        simpa)
  have hsplit : (δ / 2) ^ (-(1 / (p : ℝ))) =
      δ ^ (-(1 / (p : ℝ))) * (2 : ℝ) ^ (1 / (p : ℝ)) := by
    rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
  have hconst : (32 * Real.exp 2 * (p : ℝ)) ^ 2 =
      1024 * Real.exp 4 * (p : ℝ) ^ 2 := by
    have h : (Real.exp 2) ^ 2 = Real.exp 4 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    simp only [mul_pow, h]
    ring
  have hraw : (32 * Real.exp 2 * (p : ℝ)) ^ 2 * (δ / 2) ^ (-(1 / (p : ℝ))) ≤
      2048 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by
    rw [hconst, hsplit]
    have := mul_le_mul_of_nonneg_left htwo
      (show 0 ≤ 1024 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) by positivity)
    nlinarith
  have hfloor : (shiftOrder δ p : ℝ) <
      (32 * Real.exp 2 * (p : ℝ)) ^ 2 * (δ / 2) ^ (-(1 / (p : ℝ))) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hunit : 1 ≤ Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by
    calc
      (1 : ℝ) = 1 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  nlinarith

/-- The finite universal constant in the logarithmic approximation cost. -/
def approximationLogConstant : ℝ := 2097152 * Real.exp 4

theorem approximationLogConstant_pos : 0 < approximationLogConstant := by
  unfold approximationLogConstant
  positivity

/-- Substitution of the actual shift order gives the logarithmic cost used in
restricted-energy distribution recurrences. -/
theorem log_restrictedApproximationConstant_shiftOrder_le
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (restrictedApproximationConstant (shiftOrder δ p) δ) ≤
      approximationLogConstant * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log (approximationLogConstant * (p : ℝ) / δ) := by
  let K : ℝ := 4096 * Real.exp 4
  let C : ℝ := approximationLogConstant
  let D : ℝ := δ ^ (-(1 / (p : ℝ)))
  let n : ℕ := shiftOrder δ p
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 4 by norm_num)]
  have hCeq : C = 512 * K := by dsimp [C, K, approximationLogConstant]; ring
  have hC : 1 ≤ C := by rw [hCeq]; linarith
  have hC0 : 0 < C := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
    (neg_nonpos.mpr (by positivity))
  have hDupper : D ≤ 1 / δ := by
    have he : -(1 : ℝ) ≤ -(1 / (p : ℝ)) := by
      have := (div_le_iff₀ hp0).mpr (show (1 : ℝ) ≤ 1 * p by simpa using hp1)
      linarith
    simpa only [D, Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he
  have hn : (n : ℝ) ≤ K * (p : ℝ) ^ 2 * D := shiftOrder_le hδ hδ1 p hp
  have hunit : 1 ≤ K * (p : ℝ) ^ 2 * D := by
    calc
      (1 : ℝ) = 1 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hnadd : (n : ℝ) + 1 ≤ 2 * K * (p : ℝ) ^ 2 * D := by nlinarith
  have ht : 1 ≤ C * (p : ℝ) / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hlog : 0 ≤ Real.log (C * (p : ℝ) / δ) := Real.log_nonneg ht
  have hbase : 256 * ((n : ℝ) + 1) / δ ≤ (C * (p : ℝ) / δ) ^ 2 := by
    calc
      _ ≤ 256 * (2 * K * (p : ℝ) ^ 2 * D) / δ := by gcongr
      _ = C * (p : ℝ) ^ 2 * D / δ := by rw [hCeq]; ring
      _ ≤ C * (p : ℝ) ^ 2 * (1 / δ) / δ := by gcongr
      _ = C * ((p : ℝ) / δ) ^ 2 := by ring
      _ ≤ C ^ 2 * ((p : ℝ) / δ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        nlinarith
      _ = _ := by ring
  have hbaselog : Real.log (256 * ((n : ℝ) + 1) / δ) ≤
      2 * Real.log (C * (p : ℝ) / δ) := by
    have hbpos : 0 < 256 * ((n : ℝ) + 1) / δ := by positivity
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hbpos hbase
  have hnpos : 1 ≤ n := (by omega : 1 ≤ 2).trans (two_le_shiftOrder hδ hδ1 p hp)
  have hstart := log_restrictedApproximationConstant_le hnpos hδ hδ1
  change Real.log (restrictedApproximationConstant n δ) ≤
    C * (p : ℝ) ^ 2 * D * Real.log (C * (p : ℝ) / δ)
  calc
    _ ≤ 32 * (n : ℝ) * Real.log (256 * ((n : ℝ) + 1) / δ) := hstart
    _ ≤ 32 * (n : ℝ) * (2 * Real.log (C * (p : ℝ) / δ)) := by gcongr
    _ = 64 * (n : ℝ) * Real.log (C * (p : ℝ) / δ) := by ring
    _ ≤ 64 * (K * (p : ℝ) ^ 2 * D) * Real.log (C * (p : ℝ) / δ) := by gcongr
    _ = (64 * K) * (p : ℝ) ^ 2 * D * Real.log (C * (p : ℝ) / δ) := by ring
    _ ≤ C * (p : ℝ) ^ 2 * D * Real.log (C * (p : ℝ) / δ) := by
      have h64 : 64 * K ≤ C := by rw [hCeq]; linarith
      gcongr

/-- The universal logarithmic constant has a small logarithm. -/
theorem log_approximationLogConstant_le : Real.log approximationLogConstant ≤ 25 := by
  unfold approximationLogConstant
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
    show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at *
  linarith

/-- Below the terminal measure threshold, the constant inside the logarithm
is absorbed with an explicit factor. -/
theorem log_approximation_ratio_le {δ : ℝ} (hδ : 0 < δ) (hδ9 : δ ≤ 9 / 10)
    (p : ℕ) (hp : 1 ≤ p) :
    Real.log (approximationLogConstant * (p : ℝ) / δ) ≤
      256 * Real.log ((p : ℝ) / δ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hfrac : δ / (p : ℝ) ≤ 9 / 10 :=
    (div_le_self hδ.le hp1).trans hδ9
  have hlog : (1 : ℝ) / 10 ≤ Real.log ((p : ℝ) / δ) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hδ)
    rw [inv_div] at h
    linarith
  rw [mul_div_assoc, Real.log_mul approximationLogConstant_pos.ne' (div_pos hp0 hδ).ne']
  linarith [log_approximationLogConstant_le]

/-- A constant in the exact form required for finite measure-growth recurrences. -/
def approximationRecurrenceConstant : ℝ := 536870912 * Real.exp 4

theorem approximationRecurrenceConstant_pos : 0 < approximationRecurrenceConstant := by
  unfold approximationRecurrenceConstant
  positivity

/-- The approximation cost has the moment-order and event-mass dependence
needed by the sixth-power logarithmic distribution estimate. -/
theorem log_restrictedApproximationConstant_shiftOrder_le_recurrence
    {δ : ℝ} (hδ : 0 < δ) (hδ9 : δ ≤ 9 / 10) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (restrictedApproximationConstant (shiftOrder δ p) δ) ≤
      approximationRecurrenceConstant * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log ((p : ℝ) / δ) := by
  calc
    _ ≤ approximationLogConstant * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log (approximationLogConstant * (p : ℝ) / δ) :=
      log_restrictedApproximationConstant_shiftOrder_le hδ (by linarith) p hp
    _ ≤ approximationLogConstant * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        (256 * Real.log ((p : ℝ) / δ)) := by
      apply mul_le_mul_of_nonneg_left (log_approximation_ratio_le hδ hδ9 p hp)
      exact mul_nonneg (mul_nonneg approximationLogConstant_pos.le (sq_nonneg _))
        (Real.rpow_nonneg hδ.le _)
    _ = _ := by unfold approximationRecurrenceConstant approximationLogConstant; ring

/-- Along an increasing chain of event masses, the logarithm may be evaluated
at the fixed initial mass. -/
theorem log_restrictedApproximationConstant_shiftOrder_le_initial_mass
    {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ9 : δ ≤ 9 / 10)
    (p : ℕ) (hp : 1 ≤ p) :
    Real.log (restrictedApproximationConstant (shiftOrder δ p) δ) ≤
      approximationRecurrenceConstant * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log ((p : ℝ) / δ₀) := by
  have hδ : 0 < δ := hδ₀.trans_le hδ₀δ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  refine (log_restrictedApproximationConstant_shiftOrder_le_recurrence hδ hδ9 p hp).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg approximationRecurrenceConstant_pos.le (sq_nonneg _))
      (Real.rpow_nonneg hδ.le _))
  apply Real.log_le_log (div_pos hp0 hδ)
  gcongr

end Erdos522.LogMoments

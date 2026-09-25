/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpreadingEnergy
import Erdos522.Probability.LogMoments.ApproximationConstants
import Erdos522.Analysis.DistributionGrowth

/-!
# Constants in the Fourier spreading recurrence

The exact local spreading multiplier has logarithmic cost linear in the
approximation order. At the coefficient-uniform shift order this is the
quadratic moment-order cost used by the distribution recurrence.
-/

noncomputable section
namespace Erdos522.LogMoments

/-- One power dominates the exact spreading multiplier. -/
theorem spreadingEnergyConstant_le {n : ℕ} (hn : 1 ≤ n)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) :
    spreadingEnergyConstant n δ C ≤ (256 * C * ((n : ℝ) + 1) / δ) ^ (64 * n) := by
  let x : ℝ := (n : ℝ) + 1
  let B : ℝ := 256 * C * x / δ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hx : 1 ≤ x := by dsimp only [x]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hBCx : 256 * C * x ≤ B := by
    dsimp only [B]
    apply (le_div_iff₀ hδ).mpr
    exact mul_le_of_le_one_right (by positivity) hδ1
  have hCx : x ≤ C * x := by nlinarith
  have hBx : x ≤ B := by nlinarith
  have hB1 : 1 ≤ B := hx.trans hBx
  have hB256 : 256 ≤ B := by nlinarith
  have hbase : 16 * C * (n : ℝ) / δ ≤ B := by
    dsimp only [B, x]
    gcongr <;> linarith
  have hscale : 32 * (n : ℝ) ^ 2 / δ ≤ B ^ 2 := by
    calc
      _ ≤ 256 * C * x ^ 2 / δ := by
        gcongr
        · nlinarith
        · dsimp only [x]; linarith
      _ = B * x := by dsimp only [B]; ring
      _ ≤ B * B := mul_le_mul_of_nonneg_left hBx hB0
      _ = _ := by ring
  have hR : restrictedApproximationConstant n δ ≤ B ^ (32 * n) := by
    refine (restrictedApproximationConstant_le hn hδ hδ1).trans ?_
    dsimp only [B, x]
    gcongr
    nlinarith
  have hproduct : (32 * (n : ℝ) ^ 2 / δ) ^ (2 * n) * restrictedApproximationConstant n δ ≤
      B ^ (36 * n) := by
    calc
      _ ≤ (B ^ 2) ^ (2 * n) * B ^ (32 * n) := by
        have := (restrictedApproximationConstant_pos n hδ).le
        gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hinner : 1 + (32 * (n : ℝ) ^ 2 / δ) ^ (2 * n) *
      restrictedApproximationConstant n δ ≤ B ^ (36 * n + 1) := by
    calc
      _ ≤ 2 * B ^ (36 * n) := by linarith [one_le_pow₀ hB1 (n := 36 * n)]
      _ ≤ B * B ^ (36 * n) := by gcongr; linarith
      _ = _ := by rw [pow_succ']
  have hterm : 6 * (16 * C * n / δ) ^ (2 * n + 1) *
      (1 + (32 * (n : ℝ) ^ 2 / δ) ^ (2 * n) * restrictedApproximationConstant n δ) ≤
      B ^ (38 * n + 3) := by
    calc
      _ ≤ B * B ^ (2 * n + 1) * B ^ (36 * n + 1) := by
        have := (restrictedApproximationConstant_pos n hδ).le
        gcongr
        linarith
      _ = _ := by rw [← pow_succ', ← pow_add]; congr 1; omega
  unfold spreadingEnergyConstant
  change _ ≤ B ^ (64 * n)
  calc
    _ ≤ 2 * B ^ (38 * n + 3) := by linarith [one_le_pow₀ hB1 (n := 38 * n + 3)]
    _ ≤ B * B ^ (38 * n + 3) := by gcongr; linarith
    _ = B ^ (38 * n + 4) := by
      simpa only [Nat.add_assoc] using (pow_succ' B (38 * n + 3)).symm
    _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)

/-- Logarithmic cost of the exact spreading multiplier. -/
theorem log_spreadingEnergyConstant_le {n : ℕ} (hn : 1 ≤ n)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) :
    Real.log (spreadingEnergyConstant n δ C) ≤
      64 * (n : ℝ) * Real.log (256 * C * ((n : ℝ) + 1) / δ) := by
  have hS : 0 < spreadingEnergyConstant n δ C :=
    zero_lt_one.trans_le (one_le_spreadingEnergyConstant n hδ (by linarith))
  have h := Real.log_le_log hS (spreadingEnergyConstant_le hn hδ hδ1 hC)
  simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using h

/-- Below mass `9/10`, the logarithm of the spreading base has a uniform
linear bound in the logarithm of the moment-order-to-mass ratio. -/
theorem log_spreading_base_shiftOrder_le {δ C : ℝ}
    (hδ : 0 < δ) (hδ9 : δ ≤ 9 / 10) (hC : 1 ≤ C) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (256 * C * ((shiftOrder δ p : ℝ) + 1) / δ) ≤
      (252 + 10 * Real.log C) * Real.log ((p : ℝ) / δ) := by
  let K : ℝ := 4096 * Real.exp 4
  let D : ℝ := δ ^ (-(1 / (p : ℝ)))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hC0 : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hK : 1 ≤ K := by
    dsimp only [K]
    nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 4 by norm_num)]
  have hD : 1 ≤ D := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
    (neg_nonpos.mpr (by positivity))
  have hDupper : D ≤ 1 / δ := by
    have he : -(1 : ℝ) ≤ -(1 / (p : ℝ)) := by
      have := (div_le_iff₀ hp0).mpr (show (1 : ℝ) ≤ 1 * p by simpa using hp1)
      linarith
    simpa only [D, Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he
  have hn := shiftOrder_le hδ hδ1 p hp
  have hunit : 1 ≤ K * (p : ℝ) ^ 2 * D := by
    calc
      (1 : ℝ) = 1 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hnadd : (shiftOrder δ p : ℝ) + 1 ≤ 2 * K * (p : ℝ) ^ 2 * D := by
    change (shiftOrder δ p : ℝ) ≤ K * (p : ℝ) ^ 2 * D at hn
    nlinarith
  have hbase : 256 * C * ((shiftOrder δ p : ℝ) + 1) / δ ≤
      C * approximationLogConstant * ((p : ℝ) / δ) ^ 2 := by
    calc
      _ ≤ 256 * C * (2 * K * (p : ℝ) ^ 2 * D) / δ := by gcongr
      _ ≤ 256 * C * (2 * K * (p : ℝ) ^ 2 * (1 / δ)) / δ := by gcongr
      _ = _ := by unfold approximationLogConstant; dsimp only [K]; ring
  have hlogratio : (1 : ℝ) / 10 ≤ Real.log ((p : ℝ) / δ) := by
    have hfrac : δ / (p : ℝ) ≤ 9 / 10 := (div_le_self hδ.le hp1).trans hδ9
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hδ)
    rw [inv_div] at h
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 256 * C *
    ((shiftOrder δ p : ℝ) + 1) / δ) hbase
  rw [Real.log_mul (mul_ne_zero hC0.ne' approximationLogConstant_pos.ne') (by positivity),
    Real.log_mul hC0.ne' approximationLogConstant_pos.ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith [log_approximationLogConstant_le,
    mul_nonneg hlogC (sub_nonneg.mpr hlogratio)]

/-- The finite coefficient in the logarithmic cost of one spreading step. -/
def spreadingRecurrenceConstant (C : ℝ) : ℝ :=
  262144 * Real.exp 4 * (252 + 10 * Real.log C)

theorem spreadingRecurrenceConstant_pos {C : ℝ} (hC : 1 ≤ C) :
    0 < spreadingRecurrenceConstant C := by
  have := Real.log_nonneg hC
  unfold spreadingRecurrenceConstant
  positivity

/-- The exact spreading multiplier has the quadratic moment-order cost of
the sixth-power distribution recurrence. -/
theorem log_spreadingEnergyConstant_shiftOrder_le_recurrence {δ C : ℝ}
    (hδ : 0 < δ) (hδ9 : δ ≤ 9 / 10) (hC : 1 ≤ C) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (spreadingEnergyConstant (shiftOrder δ p) δ C) ≤
      spreadingRecurrenceConstant C * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log ((p : ℝ) / δ) := by
  have hδ1 : δ ≤ 1 := by linarith
  have hn : 1 ≤ shiftOrder δ p := (by omega : 1 ≤ 2).trans (two_le_shiftOrder hδ hδ1 p hp)
  have hlog : 0 ≤ Real.log ((p : ℝ) / δ) := Real.log_nonneg
    ((one_le_div hδ).mpr (hδ1.trans (by exact_mod_cast hp)))
  have hlogC := Real.log_nonneg hC
  calc
    _ ≤ 64 * (shiftOrder δ p : ℝ) *
        Real.log (256 * C * ((shiftOrder δ p : ℝ) + 1) / δ) :=
      log_spreadingEnergyConstant_le hn hδ hδ1 hC
    _ ≤ 64 * (shiftOrder δ p : ℝ) *
        ((252 + 10 * Real.log C) * Real.log ((p : ℝ) / δ)) := by
      exact mul_le_mul_of_nonneg_left (log_spreading_base_shiftOrder_le hδ hδ9 hC p hp)
        (by positivity)
    _ ≤ 64 * (4096 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ)))) *
        ((252 + 10 * Real.log C) * Real.log ((p : ℝ) / δ)) := by
      gcongr
      exact shiftOrder_le hδ hδ1 p hp
    _ = _ := by unfold spreadingRecurrenceConstant; ring

/-- A growing chain may evaluate the logarithm at its initial mass. -/
theorem log_spreadingEnergyConstant_shiftOrder_le_initial_mass {δ₀ δ C : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ9 : δ ≤ 9 / 10)
    (hC : 1 ≤ C) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (spreadingEnergyConstant (shiftOrder δ p) δ C) ≤
      spreadingRecurrenceConstant C * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) *
        Real.log ((p : ℝ) / δ₀) := by
  have hδ := hδ₀.trans_le hδ₀δ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  refine (log_spreadingEnergyConstant_shiftOrder_le_recurrence hδ hδ9 hC p hp).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (spreadingRecurrenceConstant_pos hC).le (sq_nonneg _))
      (Real.rpow_nonneg hδ.le _))
  apply Real.log_le_log (div_pos hp0 hδ)
  gcongr

/-- The universal measure-growth coefficient supplied by the critical order. -/
def spreadingIncrementConstant : ℝ := 1 / (16384 * Real.exp 4)

theorem spreadingIncrementConstant_pos : 0 < spreadingIncrementConstant := by
  unfold spreadingIncrementConstant
  positivity

theorem spreadingIncrementConstant_le_ninth : spreadingIncrementConstant ≤ 1 / 9 := by
  unfold spreadingIncrementConstant
  have he := Real.one_le_exp (show (0 : ℝ) ≤ 4 by norm_num)
  apply (div_le_div_iff₀ (by positivity : 0 < 16384 * Real.exp 4) (by norm_num)).mpr
  nlinarith

/-- The critical-shift gain dominates the increment required by the
reciprocal-power distribution potential. -/
theorem distributionStep_le_critical_gain {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) :
    Erdos522.distributionStep (p : ℝ) spreadingIncrementConstant δ ≤
      δ / (4 * (shiftOrder δ p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hn0 : (0 : ℝ) < shiftOrder δ p := by
    exact_mod_cast (show 0 < shiftOrder δ p by have := two_le_shiftOrder hδ hδ1 p hp; omega)
  have hn := shiftOrder_le hδ hδ1 p hp
  calc
    _ = δ / (4 * (4096 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))))) := by
      unfold Erdos522.distributionStep spreadingIncrementConstant
      rw [Real.rpow_add hδ, Real.rpow_one, Real.rpow_neg hδ.le]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_left hδ.le (by positivity)
      (mul_le_mul_of_nonneg_left hn (by norm_num))

/-- The recurrence coefficient absorbs the elementary terminal-energy cost. -/
theorem thirty_two_le_spreadingRecurrenceConstant {C : ℝ} (hC : 1 ≤ C) :
    32 ≤ spreadingRecurrenceConstant C := by
  have hlog := Real.log_nonneg hC
  unfold spreadingRecurrenceConstant
  calc
    (32 : ℝ) ≤ 262144 * 1 * 252 := by norm_num
    _ ≤ _ := by
      gcongr
      · exact Real.one_le_exp (by norm_num)
      · linarith

/-- The branch with restricted energy at least `δ/4` has no greater
logarithmic cost than a spreading step. -/
theorem log_four_div_le_spreading_cost {δ₀ δ C : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ9 : δ ≤ 9 / 10)
    (hC : 1 ≤ C) (p : ℕ) (hp : 1 ≤ p) :
    Real.log (4 / δ) ≤ spreadingRecurrenceConstant C * (p : ℝ) ^ 2 *
      δ ^ (-(1 / (p : ℝ))) * Real.log ((p : ℝ) / δ₀) := by
  have hδ : 0 < δ := hδ₀.trans_le hδ₀δ
  have hδ1 : δ ≤ 1 := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hL : (1 : ℝ) / 10 ≤ Real.log ((p : ℝ) / δ) := by
    have hfrac : δ / (p : ℝ) ≤ 9 / 10 := (div_le_self hδ.le hp1).trans hδ9
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hδ)
    rw [inv_div] at h
    linarith
  have hfour : Real.log (4 / δ) ≤ 32 * Real.log ((p : ℝ) / δ) := by
    have hlogp := Real.log_nonneg hp1
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at *
      linarith
    rw [Real.log_div (by norm_num) hδ.ne']
    rw [Real.log_div hp0.ne' hδ.ne'] at hL ⊢
    nlinarith
  have hSC0 := (spreadingRecurrenceConstant_pos hC).le
  have hcoef : 32 ≤ spreadingRecurrenceConstant C * (p : ℝ) ^ 2 *
      δ ^ (-(1 / (p : ℝ))) := by
    calc
      (32 : ℝ) = 32 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by
        gcongr
        · exact thirty_two_le_spreadingRecurrenceConstant hC
        · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
            (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ 32 * Real.log ((p : ℝ) / δ) := hfour
    _ ≤ (spreadingRecurrenceConstant C * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ)))) *
        Real.log ((p : ℝ) / δ) := mul_le_mul_of_nonneg_right hcoef (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.log_le_log (div_pos hp0 hδ)
      gcongr

end Erdos522.LogMoments

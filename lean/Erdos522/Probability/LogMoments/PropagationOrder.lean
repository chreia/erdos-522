/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.QuantitativeShifts
import Erdos522.Probability.LogMoments.RestrictedEnergyDichotomy

/-!
# A common order for the restricted-energy dichotomy

The spectral shift order is large enough for the long-section estimate.
Thus the same parameter controls both branches of the restricted-energy argument.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The shift order dominates the order required to control the missing parts of long sections. -/
theorem longSectionOrder_le_shiftOrder {δ : ℝ} (hδ : 0 < δ) (p : ℕ) (hp : 1 ≤ p) :
    512 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) ≤ shiftOrder δ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hexp : (Real.exp 2) ^ 2 = Real.exp 4 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hconst : (32 * Real.exp 2 * (p : ℝ)) ^ 2 = 1024 * Real.exp 4 * (p : ℝ) ^ 2 := by
    simp only [mul_pow, hexp]
    ring
  calc
    _ ≤ 1024 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by
      gcongr
      norm_num
    _ ≤ (32 * Real.exp 2 * (p : ℝ)) ^ 2 * (δ / 2) ^ (-(1 / (p : ℝ))) := by
      rw [hconst]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
        (neg_nonpos.mpr (by positivity))
    _ ≤ shiftOrder δ p := Nat.le_ceil _

/-- Positive event probabilities give shift order at least two. -/
theorem two_le_shiftOrder {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) : 2 ≤ shiftOrder δ p := by
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : 1 ≤ δ ^ (-(1 / (p : ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
      (neg_nonpos.mpr (by positivity))
  have hbase : (2 : ℝ) ≤ 512 * Real.exp 4 * (p : ℝ) ^ 2 * δ ^ (-(1 / (p : ℝ))) := by
    calc
      (2 : ℝ) ≤ 512 * 1 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by
        gcongr
        exact Real.one_le_exp (by norm_num)
  exact_mod_cast hbase.trans (longSectionOrder_le_shiftOrder hδ p hp)

/-- At the spectral shift order, either an angular translate gains substantial
    measure or every normalized coefficient vector already has sufficient restricted energy. -/
theorem restricted_energy_dichotomy_at_shiftOrder {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p) :
    (∃ t : AddCircle (1 : ℝ), (fourierMeasure N).real E /
      (2 * (shiftOrder ((fourierMeasure N).real E) p : ℝ)) ≤ angularTranslationLoss E t) ∨
    (∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      (fourierMeasure N).real E / 4 ≤
        ∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) := by
  apply restricted_energy_dichotomy E hE hpos p hp
  · exact_mod_cast two_le_shiftOrder hpos measureReal_le_one p hp
  · exact longSectionOrder_le_shiftOrder hpos p hp

end Erdos522.LogMoments

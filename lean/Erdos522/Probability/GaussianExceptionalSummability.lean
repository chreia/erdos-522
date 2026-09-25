/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianAnnularSmallDerivativeRate
import Erdos522.Probability.RealPowerConcentration

/-!
# Summable Gaussian exceptional probabilities

The coefficient truncation has Gaussian decay, and the energy exception has
geometric decay. Both remain summable on every injective degree schedule;
the annular mesh term retains the polynomial sparse-degree threshold.
-/

noncomputable section
open Filter
namespace Erdos522

/-- The Gaussian coefficient-truncation exceptions are summable over every degree. -/
theorem summable_gaussian_coefficient_truncation_failure :
    Summable (fun N : ℕ => 2 * (N + 1) * Real.exp (-(N : ℝ) ^ 2 / 2)) := by
  have h₁ := (Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left 2
  have h₂ := (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-(1 / 2) : ℝ) < 0)).mul_left 2
  have hs : Summable (fun N : ℕ => 2 * (N + 1) * Real.exp (-(1 / 2 : ℝ) * N)) := by
    apply (h₁.add h₂).congr
    intro N
    simp only [pow_one]
    rw [mul_comm (N : ℝ) (-(1 / 2 : ℝ))]
    ring
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The exceptional lower energy probabilities are summable over every degree. -/
theorem summable_gaussian_lower_energy_failure :
    Summable (fun N : ℕ => Real.exp (-3 * (N + 1 : ℝ) / 32)) := by
  have h := (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-(3 / 32) : ℝ) < 0)).mul_right
    (Real.exp (-(3 / 32 : ℝ)))
  apply h.congr
  intro N
  rw [← Real.exp_add]
  congr 1
  ring

/-- The complete Gaussian annular derivative envelope is summable at the
same rounded-power exponents as the mesh variance estimate. -/
theorem summable_real_power_gaussian_annular_derivative_failure {q : ℝ}
    (hq : 8 / 3 < q) (C : ℝ) :
    Summable (fun j : ℕ => gaussianAnnularDerivativeFailure C (realPowerDegree q j)) := by
  have hi := (strictMono_realPowerDegree (show 1 ≤ q by linarith)).injective
  exact ((summable_real_power_annular_failure_envelope hq C).add
    (summable_gaussian_lower_energy_failure.comp_injective hi)).add
      (summable_gaussian_coefficient_truncation_failure.comp_injective hi)

/-- The complete Gaussian annular derivative envelope is summable on eighth-power degrees. -/
theorem summable_eighth_power_gaussian_annular_derivative_failure (C : ℝ) :
    Summable (fun j : ℕ => gaussianAnnularDerivativeFailure C (j ^ 8)) := by
  have h := summable_real_power_gaussian_annular_derivative_failure (q := 8) (by norm_num) C
  convert h using 1
  ext j
  congr 1
  unfold realPowerDegree
  norm_num [← Nat.cast_pow]

end Erdos522

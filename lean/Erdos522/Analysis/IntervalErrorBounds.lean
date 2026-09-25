/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scaling interval remainders

An integral remainder of order `k` on an interval of length `Mτ` is a
scaled cell average. If `1 ≤ k ≤ m` and `M ≥ 1`, its scale is bounded by `M^m`.
-/

namespace Erdos522

/-- Exact conversion of an integral remainder to a scaled average. -/
theorem interval_remainder_eq_scaled_average {ℓ M τ I : ℝ} {k : ℕ}
    (hℓ : ℓ = M * τ) (hM : M ≠ 0) (hτ : τ ≠ 0) (hk : 0 < k) :
    ℓ ^ (k - 1) * I = M ^ k * (τ ^ k * (I / ℓ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  rw [hℓ]
  simp only [Nat.succ_sub_one, pow_succ, mul_pow]
  field_simp

/-- The maximal order controls all scaled remainders on a fixed partition. -/
theorem interval_remainder_le_scaled_average {ℓ M τ I : ℝ} {k m : ℕ}
    (hℓ : ℓ = M * τ) (hM : 1 ≤ M) (hτ : 0 < τ) (hk : 0 < k) (hkm : k ≤ m)
    (hI : 0 ≤ I) :
    ℓ ^ (k - 1) * I ≤ M ^ m * (τ ^ k * (I / ℓ)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
  rw [interval_remainder_eq_scaled_average hℓ hMpos.ne' hτ.ne' hk]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hkm)
    (mul_nonneg (pow_nonneg hτ.le _) (div_nonneg hI hℓpos.le))

end Erdos522

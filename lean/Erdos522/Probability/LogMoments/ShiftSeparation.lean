/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.ShiftPolynomials
import Erdos522.Analysis.SeparatedInterpolation

/-!
# Separation of sampled Fourier multipliers

If `n + 1` Fourier phases are separated, a normalized relation polynomial
has a definite total energy at those phases. Thus small simultaneous
multiplier values force a pair of phases to approach each other.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace Erdos522.LogMoments

/-- A normalized relation has definite multiplier energy at separated phases. -/
theorem shift_multiplier_energy_ge_of_separation {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∑ j, ‖c j‖ ^ 2 = 1)
    (m : Fin (n + 1) → ℕ) (t : AddCircle (1 : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖fourier (m i) t - fourier (m j) t‖) :
    (δ / 2) ^ (2 * n) / (n + 1 : ℝ) ≤ ∑ i, ‖shiftMultiplier c t (m i)‖ ^ 2 := by
  obtain ⟨z, hz, hlarge⟩ := exists_unitCircle_polynomial_norm_ge_one c hc
  simp only [shiftMultiplier_eq_polynomial_eval]
  exact polynomial_separated_energy_lower_bound _
    (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) c)) _
    (fun i => by rw [fourier_apply, Circle.norm_coe]) hδ hsep hz.le hlarge

/-- Small simultaneous multiplier values require a close pair of sampled phases. -/
theorem exists_close_phases_of_small_shift_energy {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∑ j, ‖c j‖ ^ 2 = 1)
    (m : Fin (n + 1) → ℕ) (t : AddCircle (1 : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : (∑ i, ‖shiftMultiplier c t (m i)‖ ^ 2) <
      (δ / 2) ^ (2 * n) / (n + 1 : ℝ)) :
    ∃ i j, i ≠ j ∧ ‖fourier (m i) t - fourier (m j) t‖ < δ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hsmall)
    (shift_multiplier_energy_ge_of_separation c hc m t hδ h)

end Erdos522.LogMoments

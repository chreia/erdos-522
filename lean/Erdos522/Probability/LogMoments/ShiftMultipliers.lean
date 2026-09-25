/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SmallShifts

/-!
# Fourier multipliers of finite shift combinations

A normalized linear relation among angular shifts acts on each coefficient by
one polynomial in its Fourier character. Parseval converts the shift energy
into the corresponding weighted multiplier energy.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The Fourier multiplier associated with a finite shift combination. -/
def shiftMultiplier {n : ℕ} (c : Fin (n + 1) → ℂ)
    (t : AddCircle (1 : ℝ)) (k : ℕ) : ℂ :=
  ∑ j, c j * fourier k (j.val • t)

/-- A finite sum of shifted Fourier polynomials is one Fourier polynomial. -/
theorem sum_shifted_randomFourier {N n : ℕ} (a : Fin (N + 1) → ℂ)
    (c : Fin (n + 1) → ℂ) (t : AddCircle (1 : ℝ))
    (q : SignVector N × AddCircle (1 : ℝ)) :
    (∑ j, c j * randomFourier a (angularTranslation N (j.val • t) q)) =
      randomFourier (fun k => a k * shiftMultiplier c t k.val) q := by
  have ht (j : Fin (n + 1)) : randomFourier a (angularTranslation N (j.val • t) q) =
      randomFourier (translatedCoefficients a (j.val • t)) q :=
    (fourierPolynomial_translatedCoefficients a (j.val • t) q.2 q.1).symm
  simp_rw [ht]
  rw [← randomFourier_sum_mul]
  congr 1
  funext k
  simp only [shiftMultiplier, translatedCoefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Parseval's exact weighted-multiplier formula for the small-shift energy. -/
theorem integral_shift_combination_eq_multiplier_energy {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (c : Fin (n + 1) → ℂ) (t : AddCircle (1 : ℝ)) :
    (∫ q, ‖∑ j, c j * randomFourier a (angularTranslation N (j.val • t) q)‖ ^ 2
      ∂fourierMeasure N) = ∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier c t k.val‖ ^ 2 := by
  simp_rw [sum_shifted_randomFourier]
  rw [integral_norm_sq_randomFourier]
  simp only [norm_mul, mul_pow]

/-- The weighted multiplier energy depends continuously on the shift and relation coefficients. -/
theorem continuous_shift_multiplier_energy {N n : ℕ} (a : Fin (N + 1) → ℂ) :
    Continuous (fun p : AddCircle (1 : ℝ) × (Fin (n + 1) → ℂ) =>
      ∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier p.2 p.1 k.val‖ ^ 2) := by
  unfold shiftMultiplier
  fun_prop

end Erdos522.LogMoments

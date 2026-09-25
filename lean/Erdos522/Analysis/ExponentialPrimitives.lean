/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialIntegration

/-!
# Integrating exponential functions

Integrating a character against a different frequency produces a linear
combination of the two characters. This identity underlies finite-dimensional
exponential approximation on an interval.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

@[simp] theorem oscillatoryPrimitive_zero (ξ a : ℝ) :
    oscillatoryPrimitive ξ a 0 = 0 := by
  funext x
  simp [oscillatoryPrimitive]

/-- Continuous summands may be integrated separately. -/
theorem oscillatoryPrimitive_add (ξ a : ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    oscillatoryPrimitive ξ a (f + g) =
      oscillatoryPrimitive ξ a f + oscillatoryPrimitive ξ a g := by
  funext x
  have hf' : IntervalIntegrable (fun t => angularCharacter (-ξ * t) * f t) volume a x :=
    ((continuous_angularCharacter_mul (-ξ)).mul hf).intervalIntegrable a x
  have hg' : IntervalIntegrable (fun t => angularCharacter (-ξ * t) * g t) volume a x :=
    ((continuous_angularCharacter_mul (-ξ)).mul hg).intervalIntegrable a x
  simp only [oscillatoryPrimitive, Pi.add_apply, mul_add]
  rw [intervalIntegral.integral_add hf' hg']
  ring

/-- Continuous differences may be integrated separately. -/
theorem oscillatoryPrimitive_sub (ξ a : ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    oscillatoryPrimitive ξ a (f - g) =
      oscillatoryPrimitive ξ a f - oscillatoryPrimitive ξ a g := by
  funext x
  have hf' : IntervalIntegrable (fun t => angularCharacter (-ξ * t) * f t) volume a x :=
    ((continuous_angularCharacter_mul (-ξ)).mul hf).intervalIntegrable a x
  have hg' : IntervalIntegrable (fun t => angularCharacter (-ξ * t) * g t) volume a x :=
    ((continuous_angularCharacter_mul (-ξ)).mul hg).intervalIntegrable a x
  simp only [oscillatoryPrimitive, Pi.sub_apply]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hf' hg']
  ring

/-- Constant factors pass through an oscillatory primitive. -/
theorem oscillatoryPrimitive_const_mul (ξ a : ℝ) (c : ℂ) (h : ℝ → ℂ) (x : ℝ) :
    oscillatoryPrimitive ξ a (fun t => c * h t) x = c * oscillatoryPrimitive ξ a h x := by
  unfold oscillatoryPrimitive
  simp_rw [show ∀ t, angularCharacter (-ξ * t) * (c * h t) =
    c * (angularCharacter (-ξ * t) * h t) by intro t; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

@[simp] theorem frequencyMultiplier_sub (η ξ : ℝ) :
    frequencyMultiplier (η - ξ) = frequencyMultiplier η - frequencyMultiplier ξ := by
  simp only [frequencyMultiplier, Complex.ofReal_sub, mul_sub]

theorem frequencyMultiplier_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    frequencyMultiplier ξ ≠ 0 := by
  unfold frequencyMultiplier
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hξ)

/-- The undivided integrating-factor identity also covers equal frequencies. -/
theorem frequencyMultiplier_mul_primitive_character (ξ η a x : ℝ) :
    frequencyMultiplier (η - ξ) *
      oscillatoryPrimitive ξ a (fun t => angularCharacter (η * t)) x =
        angularCharacter (η * x) -
          angularCharacter (ξ * (x - a)) * angularCharacter (η * a) := by
  have hh : Continuous (fun t => frequencyMultiplier (η - ξ) * angularCharacter (η * t)) :=
    continuous_const.mul (continuous_angularCharacter_mul η)
  have hd (y : ℝ) (_hy : y ∈ Set.uIcc a x) :
      HasDerivAt (fun t => angularCharacter (η * t))
        (frequencyMultiplier ξ * angularCharacter (η * y) +
          frequencyMultiplier (η - ξ) * angularCharacter (η * y)) y := by
    convert hasDerivAt_angularCharacter_mul η y using 1
    rw [frequencyMultiplier_sub]
    ring
  have h := eq_character_mul_initial_add_oscillatoryPrimitive ξ hh hd
  rw [oscillatoryPrimitive_const_mul] at h
  linear_combination -h

/-- A nonresonant primitive is a linear combination of its forcing and integrating frequencies. -/
theorem oscillatoryPrimitive_character (ξ η a x : ℝ) (hne : η ≠ ξ) :
    oscillatoryPrimitive ξ a (fun t => angularCharacter (η * t)) x =
      (angularCharacter (η * x) -
        angularCharacter (ξ * (x - a)) * angularCharacter (η * a)) /
          frequencyMultiplier (η - ξ) := by
  apply (eq_div_iff (frequencyMultiplier_ne_zero (sub_ne_zero.mpr hne))).mpr
  rw [mul_comm]
  exact frequencyMultiplier_mul_primitive_character ξ η a x

end Erdos522

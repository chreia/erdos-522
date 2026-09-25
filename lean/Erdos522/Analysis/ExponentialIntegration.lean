/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.AngularSeparation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration with a real frequency

Modulation by a character conjugates differentiation to a constant-coefficient
first-order operator. Its zero-initial-value inverse has an integral bound
independent of the frequency.
-/

noncomputable section
open MeasureTheory
open scoped Interval
namespace Erdos522

/-- The frequency multiplier in differentiation of `exp(2π i ξ x)`. -/
def frequencyMultiplier (ξ : ℝ) : ℂ := 2 * Real.pi * Complex.I * ξ

theorem hasDerivAt_angularCharacter_mul (ξ x : ℝ) :
    HasDerivAt (fun y : ℝ => angularCharacter (ξ * y))
      (frequencyMultiplier ξ * angularCharacter (ξ * x)) x := by
  have h := (hasDerivAt_fourier (1 : ℝ) 1 (ξ * x)).scomp x
    ((hasDerivAt_id x).const_mul ξ)
  convert h using 1
  · rfl
  · simp only [angularCharacter, frequencyMultiplier,
      Int.cast_one, Complex.ofReal_one, mul_one, div_one, Complex.real_smul]
    ring

theorem continuous_angularCharacter_mul (ξ : ℝ) :
    Continuous (fun x : ℝ => angularCharacter (ξ * x)) :=
  (show Differentiable ℝ (fun x : ℝ => angularCharacter (ξ * x)) from
    fun x => (hasDerivAt_angularCharacter_mul ξ x).differentiableAt).continuous

/-- Integration after modulation, followed by the inverse modulation. -/
def oscillatoryPrimitive (ξ a : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  angularCharacter (ξ * x) * ∫ t in a..x, angularCharacter (-ξ * t) * h t

@[simp] theorem oscillatoryPrimitive_self (ξ a : ℝ) (h : ℝ → ℂ) :
    oscillatoryPrimitive ξ a h a = 0 := by simp [oscillatoryPrimitive]

/-- The integrating-factor inverse has frequency-independent integral norm. -/
theorem norm_oscillatoryPrimitive_le (ξ : ℝ) {a x : ℝ} (hax : a ≤ x) (h : ℝ → ℂ) :
    ‖oscillatoryPrimitive ξ a h x‖ ≤ ∫ t in a..x, ‖h t‖ := by
  unfold oscillatoryPrimitive
  rw [norm_mul, norm_angularCharacter, one_mul]
  simpa only [norm_mul, norm_angularCharacter, one_mul] using
    (intervalIntegral.norm_integral_le_integral_norm hax
      (f := fun t => angularCharacter (-ξ * t) * h t))

/-- The primitive solves the first-order inhomogeneous equation. -/
theorem hasDerivAt_oscillatoryPrimitive (ξ a : ℝ) {h : ℝ → ℂ}
    (hh : Continuous h) (x : ℝ) :
    HasDerivAt (oscillatoryPrimitive ξ a h)
      (frequencyMultiplier ξ * oscillatoryPrimitive ξ a h x + h x) x := by
  have hg : Continuous (fun t => angularCharacter (-ξ * t) * h t) :=
    (continuous_angularCharacter_mul (-ξ)).mul hh
  have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hp := (hasDerivAt_angularCharacter_mul ξ x).mul hi
  have he : angularCharacter (ξ * x) * angularCharacter (-ξ * x) = 1 := by
    rw [← angularCharacter_add, show ξ * x + -ξ * x = 0 by ring]
    simp [angularCharacter_eq, unitCirclePoint]
  have hc : angularCharacter (ξ * x) * (angularCharacter (-ξ * x) * h x) = h x := by
    rw [← mul_assoc, he, one_mul]
  convert! hp using 1
  simp only [oscillatoryPrimitive, mul_assoc, hc]

/-- The integrating-factor formula for a first-order equation on an interval. -/
theorem eq_character_mul_initial_add_oscillatoryPrimitive
    (ξ : ℝ) {a x : ℝ} {f h : ℝ → ℂ}
    (hh : Continuous h)
    (hf : ∀ y ∈ Set.uIcc a x,
      HasDerivAt f (frequencyMultiplier ξ * f y + h y) y) :
    f x = angularCharacter (ξ * (x - a)) * f a + oscillatoryPrimitive ξ a h x := by
  have hd (y : ℝ) (hy : y ∈ Set.uIcc a x) :
      HasDerivAt (fun t => angularCharacter (-ξ * t) * f t)
        (angularCharacter (-ξ * y) * h y) y := by
    convert! (hasDerivAt_angularCharacter_mul (-ξ) y).mul (hf y hy) using 1
    simp only [frequencyMultiplier, Complex.ofReal_neg]
    ring
  have hg := (continuous_angularCharacter_mul (-ξ)).mul hh
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.intervalIntegrable a x)
  have he (y : ℝ) : angularCharacter (ξ * y) * angularCharacter (-ξ * y) = 1 := by
    rw [← angularCharacter_add, show ξ * y + -ξ * y = 0 by ring]
    simp [angularCharacter_eq, unitCirclePoint]
  have hphase : angularCharacter (ξ * (x - a)) =
      angularCharacter (ξ * x) * angularCharacter (-ξ * a) := by
    rw [← angularCharacter_add]
    congr 1
    ring
  unfold oscillatoryPrimitive
  rw [hi, hphase, mul_sub (angularCharacter (ξ * x)),
    ← mul_assoc (angularCharacter (ξ * x)) (angularCharacter (-ξ * x)), he, one_mul]
  ring

/-- One frequency approximates a solution with an error controlled by its forcing. -/
theorem norm_sub_character_initial_le (ξ : ℝ) {a x : ℝ} (hax : a ≤ x)
    {f h : ℝ → ℂ} (hh : Continuous h)
    (hf : ∀ y ∈ Set.uIcc a x,
      HasDerivAt f (frequencyMultiplier ξ * f y + h y) y) :
    ‖f x - angularCharacter (ξ * (x - a)) * f a‖ ≤ ∫ t in a..x, ‖h t‖ := by
  have heq := eq_character_mul_initial_add_oscillatoryPrimitive ξ hh hf
  have hsub : f x - angularCharacter (ξ * (x - a)) * f a =
      oscillatoryPrimitive ξ a h x := by rw [heq]; ring
  rw [hsub]
  exact norm_oscillatoryPrimitive_le ξ hax h

end Erdos522

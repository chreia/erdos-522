/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialSpan
import Erdos522.Analysis.ComplexExponentialPropagation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Affine normalization of harmonic exponential polynomials

Finite-dimensional span membership gives a coefficient representation on the
prescribed frequency family. Affine substitution changes the coefficients by
a phase and scales the frequencies, preserving their purely imaginary nature.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- The real harmonic character is the restriction of its entire exponential. -/
theorem angularCharacter_mul_eq_exp (ξ x : ℝ) :
    angularCharacter (ξ * x) = Complex.exp (frequencyMultiplier ξ * (x : ℂ)) := by
  rw [angularCharacter_eq]
  unfold unitCirclePoint frequencyMultiplier
  congr 1
  push_cast
  ring

@[simp] theorem frequencyMultiplier_re (ξ : ℝ) : (frequencyMultiplier ξ).re = 0 := by
  simp [frequencyMultiplier, Complex.mul_re, Complex.mul_im]

/-- A function in a finite frequency span has coefficients on that same family. -/
theorem exists_complexExponentialSum_of_mem_exponentialSpan
    {ι : Type*} [Fintype ι] (ξ : ι → ℝ) {P : ℝ → ℂ}
    (hP : P ∈ exponentialSpan (Set.range ξ)) :
    ∃ c : ι → ℂ, ∀ x : ℝ,
      P x = complexExponentialSum Finset.univ c (fun j => frequencyMultiplier (ξ j)) x := by
  have hrange : (fun η x => angularCharacter (η * x)) '' Set.range ξ =
      Set.range (fun j x => angularCharacter (ξ j * x)) := by
    ext f
    constructor
    · rintro ⟨η, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨ξ j, ⟨j, rfl⟩, rfl⟩
  rw [exponentialSpan, hrange, Submodule.mem_span_range_iff_exists_fun] at hP
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun x => ?_⟩
  have hx := congrFun hc x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    angularCharacter_mul_eq_exp, complexExponentialSum] using hx.symm

/-- Affine substitution keeps the same number of exponential terms. -/
theorem complexExponentialSum_affine {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a l z : ℂ) :
    complexExponentialSum s c ζ (a + l * z) =
      complexExponentialSum s (fun j => c j * Complex.exp (ζ j * a))
        (fun j => ζ j * l) z := by
  unfold complexExponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_add, Complex.exp_add, mul_assoc (ζ j) l z, mul_assoc]

/-- Real affine scaling preserves a purely imaginary spectrum. -/
theorem purelyImaginary_spectrum_affine {ι : Type*} (ζ : ι → ℂ)
    (hζ : ∀ j, (ζ j).re = 0) (l : ℝ) (j : ι) :
    (ζ j * (l : ℂ)).re = 0 := by
  simp [Complex.mul_re, hζ j]

end Erdos522

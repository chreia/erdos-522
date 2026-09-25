/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ComplexExponentialPropagation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differential pruning of exponential polynomials

Subtracting one spectral frequency from the derivative removes the
corresponding exponential term. Two well-separated choices of frequency
recover the original function, while the quotient by the function is a
normalized logarithmic derivative.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- Differentiation multiplies each exponential coefficient by its frequency. -/
theorem hasDerivAt_complexExponentialSum {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ) (z : ℂ) :
    HasDerivAt (complexExponentialSum s c ζ)
      (complexExponentialSum s (fun j => c j * ζ j) ζ z) z := by
  unfold complexExponentialSum
  convert HasDerivAt.fun_sum (fun j (_ : j ∈ s) =>
    (((hasDerivAt_id z).const_mul (ζ j)).cexp.const_mul (c j))) using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro j _
    simp only [mul_one, id_eq]
    ring

/-- A normalized first-order differential operator on an exponential polynomial. -/
def exponentialPruning {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a : ℂ) (ρ : ℝ) (z : ℂ) : ℂ :=
  (deriv (complexExponentialSum s c ζ) z - a * complexExponentialSum s c ζ z) / (ρ : ℂ)

/-- Differential pruning remains an exponential polynomial on the same finite spectrum. -/
theorem exponentialPruning_eq_sum {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a : ℂ) (ρ : ℝ) (z : ℂ) :
    exponentialPruning s c ζ a ρ z =
      complexExponentialSum s (fun j => c j * (ζ j - a) / (ρ : ℂ)) ζ z := by
  rw [exponentialPruning, (hasDerivAt_complexExponentialSum s c ζ z).deriv]
  simp only [complexExponentialSum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Choosing an existing frequency removes its term exactly, even when other
    coefficients vanish or frequencies coincide. -/
theorem exponentialPruning_eq_erase {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c ζ : ι → ℂ) (a : ι) (ρ : ℝ) (z : ℂ) :
    exponentialPruning s c ζ (ζ a) ρ z =
      complexExponentialSum (s.erase a) (fun j => c j * (ζ j - ζ a) / (ρ : ℂ)) ζ z := by
  rw [exponentialPruning_eq_sum]
  unfold complexExponentialSum
  by_cases ha : a ∈ s
  · rw [Finset.sum_erase_eq_sub ha]
    simp
  · rw [Finset.erase_eq_of_notMem ha]

/-- Two frequency choices differ by a scalar multiple of the original function. -/
theorem exponentialPruning_sub {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a b : ℂ) (ρ : ℝ) (z : ℂ) :
    exponentialPruning s c ζ a ρ z - exponentialPruning s c ζ b ρ z =
      ((b - a) / (ρ : ℂ)) * complexExponentialSum s c ζ z := by
  unfold exponentialPruning
  ring

/-- Spectral points at distance `ρ` give a norm-one recovery coefficient. -/
theorem norm_le_pruned_pair {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hab : ‖b - a‖ = ρ) (z : ℂ) :
    ‖complexExponentialSum s c ζ z‖ ≤
      ‖exponentialPruning s c ζ a ρ z‖ + ‖exponentialPruning s c ζ b ρ z‖ := by
  have h := norm_sub_le (exponentialPruning s c ζ a ρ z) (exponentialPruning s c ζ b ρ z)
  rw [exponentialPruning_sub, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ, hab, div_self hρ.ne', one_mul] at h
  exact h

/-- At least one of the two pruned polynomials retains half the value at a point. -/
theorem exists_pruned_norm_ge_half {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hab : ‖b - a‖ = ρ) (z : ℂ) :
    ‖complexExponentialSum s c ζ z‖ / 2 ≤ ‖exponentialPruning s c ζ a ρ z‖ ∨
      ‖complexExponentialSum s c ζ z‖ / 2 ≤ ‖exponentialPruning s c ζ b ρ z‖ := by
  have h := norm_le_pruned_pair s c ζ hρ hab z
  by_contra! hbad
  linarith

/-- Away from zeros, the pruning quotient is the normalized logarithmic derivative. -/
theorem exponentialPruning_div {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a : ℂ) (ρ : ℝ) (z : ℂ) (hz : complexExponentialSum s c ζ z ≠ 0) :
    exponentialPruning s c ζ a ρ z / complexExponentialSum s c ζ z =
      (deriv (complexExponentialSum s c ζ) z / complexExponentialSum s c ζ z - a) / (ρ : ℂ) := by
  unfold exponentialPruning
  by_cases hρ : (ρ : ℂ) = 0
  · simp [hρ]
  · field_simp

/-- Translating the spectrum factors out one exponential. -/
theorem complexExponentialSum_spectral_shift {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a z : ℂ) :
    complexExponentialSum s c ζ z = Complex.exp (a * z) *
      complexExponentialSum s c (fun j => ζ j - a) z := by
  simp only [complexExponentialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Complex.exp (a * z) * Complex.exp ((ζ j - a) * z) = Complex.exp (ζ j * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = c j * (Complex.exp (a * z) * Complex.exp ((ζ j - a) * z)) := by rw [he]
    _ = _ := by ring

/-- A purely imaginary spectral translation preserves the norm on the real line. -/
theorem norm_complexExponentialSum_spectral_shift {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a : ℂ) (ha : a.re = 0) (x : ℝ) :
    ‖complexExponentialSum s c ζ x‖ =
      ‖complexExponentialSum s c (fun j => ζ j - a) x‖ := by
  rw [complexExponentialSum_spectral_shift s c ζ a, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, ha]

/-- Spectral translation commutes with pruning after the selected frequency is translated. -/
theorem exponentialPruning_spectral_shift {ι : Type*} (s : Finset ι) (c ζ : ι → ℂ)
    (a b z : ℂ) (ρ : ℝ) :
    exponentialPruning s c ζ b ρ z = Complex.exp (a * z) *
      exponentialPruning s c (fun j => ζ j - a) (b - a) ρ z := by
  rw [exponentialPruning_eq_sum, complexExponentialSum_spectral_shift _ _ _ a,
    exponentialPruning_eq_sum]
  congr 1
  congr 1
  funext j
  congr 2
  ring

end Erdos522

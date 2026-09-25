/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherCoordinates
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Orthogonal off-diagonal Rademacher Fourier modes

The angular frequency separates a pair from its reversal. Together with independence
of the signs, this makes ordered off-diagonal pairs an orthonormal family.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos522.LogMoments

lemma realSign_mul_self (b : Bool) : realSign b * realSign b = 1 := by
  simpa only [pow_two] using realSign_sq b

/-- Fourth moments of distinct-pair sign products detect unordered pair equality. -/
theorem integral_four_realSigns {N : ℕ} (i j k l : Fin (N + 1))
    (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ ω : SignVector N, (realSign (ω i) * realSign (ω j)) *
      (realSign (ω k) * realSign (ω l)) ∂signMeasure N) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else 0 := by
  by_cases hik : i = k
  · subst k
    have heq (ω : SignVector N) : (realSign (ω i) * realSign (ω j)) *
        (realSign (ω i) * realSign (ω l)) = realSign (ω j) * realSign (ω l) := by
      calc
        _ = (realSign (ω i) * realSign (ω i)) *
          (realSign (ω j) * realSign (ω l)) := by ring
        _ = _ := by rw [realSign_mul_self, one_mul]
    simp_rw [heq]
    rw [integral_mul_realSign_coordinates]
    simp [Ne.symm hij]
  by_cases hil : i = l
  · subst l
    have heq (ω : SignVector N) : (realSign (ω i) * realSign (ω j)) *
        (realSign (ω k) * realSign (ω i)) = realSign (ω j) * realSign (ω k) := by
      calc
        _ = (realSign (ω i) * realSign (ω i)) *
          (realSign (ω j) * realSign (ω k)) := by ring
        _ = _ := by rw [realSign_mul_self, one_mul]
    simp_rw [heq]
    rw [integral_mul_realSign_coordinates]
    simp [hik]
  by_cases hjk : j = k
  · subst k
    have heq (ω : SignVector N) : (realSign (ω i) * realSign (ω j)) *
        (realSign (ω j) * realSign (ω l)) = realSign (ω i) * realSign (ω l) := by
      calc
        _ = (realSign (ω j) * realSign (ω j)) *
          (realSign (ω i) * realSign (ω l)) := by ring
        _ = _ := by rw [realSign_mul_self, one_mul]
    simp_rw [heq]
    rw [integral_mul_realSign_coordinates]
    simp [hij, hil]
  by_cases hjl : j = l
  · subst l
    have heq (ω : SignVector N) : (realSign (ω i) * realSign (ω j)) *
        (realSign (ω k) * realSign (ω j)) = realSign (ω i) * realSign (ω k) := by
      calc
        _ = (realSign (ω j) * realSign (ω j)) *
          (realSign (ω i) * realSign (ω k)) := by ring
        _ = _ := by rw [realSign_mul_self, one_mul]
    simp_rw [heq]
    rw [integral_mul_realSign_coordinates]
    simp [hij, hik]
  have hind := (iIndepFun_realSign N).indepFun_mul_mul
    (fun _ => measurable_of_finite _) i j k l hik hil hjk hjl
  have hfactor := hind.integral_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable
    (measurable_of_finite _).aestronglyMeasurable
  simpa [Pi.mul_apply, integral_mul_realSign_coordinates, hij, hkl, hik, hil] using hfactor

/-- The Fourier mode associated with an ordered pair of coefficient indices. -/
def pairMode {N : ℕ} (i j : Fin (N + 1))
    (q : SignVector N × AddCircle (1 : ℝ)) : ℂ :=
  sign (q.1 i) * sign (q.1 j) * fourier ((i : ℤ) - (j : ℤ)) q.2

lemma measurable_pairMode {N : ℕ} (i j : Fin (N + 1)) : Measurable (pairMode i j) := by
  have hi : Measurable (fun ω : SignVector N => sign (ω i)) := measurable_of_finite _
  have hj : Measurable (fun ω : SignVector N => sign (ω j)) := measurable_of_finite _
  unfold pairMode
  fun_prop

@[simp] lemma norm_pairMode {N : ℕ} (i j : Fin (N + 1))
    (q : SignVector N × AddCircle (1 : ℝ)) : ‖pairMode i j q‖ = 1 := by
  simp [pairMode]

lemma integrable_pairMode {N : ℕ} (i j : Fin (N + 1)) :
    Integrable (pairMode i j) (fourierMeasure N) := by
  apply Integrable.of_bound (measurable_pairMode i j).aestronglyMeasurable 1
  exact ae_of_all _ (fun q => by simp)

lemma conjugate_pairMode {N : ℕ} (i j : Fin (N + 1))
    (q : SignVector N × AddCircle (1 : ℝ)) :
    conj (pairMode i j q) = pairMode j i q := by
  have hsign (b : Bool) : conj (sign b) = sign b := by cases b <;> simp [sign]
  simp only [pairMode, map_mul, hsign, ← fourier_neg, neg_sub]
  ring

lemma integral_fourier_inner (m n : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), inner ℂ (fourier m θ) (fourier n θ)
      ∂AddCircle.haarAddCircle) = if m = n then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ))) m n
  rw [ContinuousMap.inner_toLp] at h
  exact h

/-- Sign and angular integration separate for pair-mode inner products. -/
lemma integral_inner_pairMode_factor {N : ℕ} (i j k l : Fin (N + 1)) :
    (∫ q, inner ℂ (pairMode i j q) (pairMode k l q) ∂fourierMeasure N) =
      Complex.ofReal (∫ ω : SignVector N, (realSign (ω i) * realSign (ω j)) *
        (realSign (ω k) * realSign (ω l)) ∂signMeasure N) *
      (if (i : ℤ) - (j : ℤ) = (k : ℤ) - (l : ℤ) then 1 else 0) := by
  have heq (q : SignVector N × AddCircle (1 : ℝ)) :
      inner ℂ (pairMode i j q) (pairMode k l q) =
      (((realSign (q.1 i) * realSign (q.1 j)) *
        (realSign (q.1 k) * realSign (q.1 l)) : ℝ) : ℂ) *
        inner ℂ (fourier ((i : ℤ) - (j : ℤ)) q.2)
          (fourier ((k : ℤ) - (l : ℤ)) q.2) := by
    simp only [pairMode, RCLike.inner_apply, map_mul, ← ofReal_realSign,
      Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  simp_rw [heq]
  rw [fourierMeasure]
  calc
    _ = (∫ ω : SignVector N, Complex.ofReal ((realSign (ω i) * realSign (ω j)) *
        (realSign (ω k) * realSign (ω l))) ∂signMeasure N) *
        (∫ θ : AddCircle (1 : ℝ), inner ℂ (fourier ((i : ℤ) - (j : ℤ)) θ)
          (fourier ((k : ℤ) - (l : ℤ)) θ) ∂AddCircle.haarAddCircle) :=
      integral_prod_mul _ _
    _ = _ := by rw [integral_complex_ofReal, integral_fourier_inner]

/-- Ordered off-diagonal pairs are orthonormal under the joint sign/angular law. -/
theorem integral_inner_pairMode {N : ℕ} (i j k l : Fin (N + 1))
    (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ q, inner ℂ (pairMode i j q) (pairMode k l q) ∂fourierMeasure N) =
      if i = k ∧ j = l then 1 else 0 := by
  rw [integral_inner_pairMode_factor, integral_four_realSigns i j k l hij hkl]
  by_cases hsame : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := hsame
    simp
  · by_cases hreverse : i = l ∧ j = k
    · obtain ⟨rfl, rfl⟩ := hreverse
      have hfreq : (i : ℤ) - (j : ℤ) ≠ (j : ℤ) - (i : ℤ) := by
        intro h
        have hv : (i : ℤ) = (j : ℤ) := by omega
        exact hij (Fin.ext (by exact_mod_cast hv))
      simp [hsame, hfreq]
    · simp [hsame, hreverse]

end Erdos522.LogMoments

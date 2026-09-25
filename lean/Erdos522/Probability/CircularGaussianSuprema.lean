/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianRepresentation
import Erdos522.Probability.GaussianDerivativeSupremum
import Erdos522.Probability.GaussianTailSupremum
import Erdos522.Probability.BoundedTailSupremum

/-!
# Derivative and appended-tail bounds for circular Gaussian polynomials

The real-coordinate representation transfers the two real Gaussian supremum
bounds. The complex envelopes are doubled, and the exceptional probabilities
are the sums of the two real-coordinate exceptional probabilities.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522

/-- A circular Gaussian polynomial is the normalized sum of two real Gaussian polynomials. -/
theorem ofFn_circularGaussianCoefficientVector (N : ℕ)
    (g : (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
    Polynomial.ofFn (N + 1) (circularGaussianCoefficientVectorEquiv (N + 1) g) =
      C ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * gaussianPolynomial N g.1 +
      C (Complex.I / (Real.sqrt 2 : ℂ)) * gaussianPolynomial N g.2 := by
  have he : circularGaussianCoefficientVectorEquiv (N + 1) g =
      ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • (fun k => (g.1 k : ℂ)) +
        (Complex.I / (Real.sqrt 2 : ℂ)) • (fun k => (g.2 k : ℂ)) := by
    funext k
    simp only [circularGaussianCoefficientVectorEquiv_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_smul, map_smul]
  simp only [Polynomial.smul_eq_C_mul, Polynomial.ofFn_eq_sum_monomial, gaussianPolynomial]

/-- Normalized real-coordinate assembly costs at most the sum of the coordinate norms. -/
theorem norm_circular_assembly_le (u v : ℂ) :
    ‖((1 : ℂ) / (Real.sqrt 2 : ℂ)) * u + (Complex.I / (Real.sqrt 2 : ℂ)) * v‖ ≤ ‖u‖ + ‖v‖ := by
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hi : (Real.sqrt 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  calc
    _ ≤ ‖((1 : ℂ) / (Real.sqrt 2 : ℂ)) * u‖ +
        ‖(Complex.I / (Real.sqrt 2 : ℂ)) * v‖ := norm_add_le _ _
    _ = (Real.sqrt 2)⁻¹ * ‖u‖ + (Real.sqrt 2)⁻¹ * ‖v‖ := by
      simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg 2)]
    _ ≤ ‖u‖ + ‖v‖ := by nlinarith [norm_nonneg u, norm_nonneg v]

/-- The complex second derivative is bounded by the two coordinate derivatives. -/
theorem circularGaussian_second_derivative_norm_le (N : ℕ)
    (g : (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) (z : ℂ) :
    ‖(Polynomial.ofFn (N + 1) (circularGaussianCoefficientVectorEquiv (N + 1) g)).derivative.derivative.eval z‖ ≤
      ‖(gaussianPolynomial N g.1).derivative.derivative.eval z‖ +
      ‖(gaussianPolynomial N g.2).derivative.derivative.eval z‖ := by
  rw [ofFn_circularGaussianCoefficientVector]
  simp only [derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
  exact norm_circular_assembly_le _ _

/-- The second-derivative envelope holds throughout the enlarged disk. -/
theorem circularGaussian_second_derivative_supremum (N : ℕ) (hN : 2 ≤ N) {K : ℝ}
    (hK : 0 ≤ K) (hKN : K + 1 ≤ (N : ℝ)) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real {a | ∃ z : ℂ,
      ‖z‖ ≤ 1 + (K + 1) / N ∧ 2 * DerivativeSupremum.secondDerivativeEnvelope N K <
        ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.eval z‖} ≤
      2 / (N : ℝ) ^ 10 + 4 * (N + 1) * Real.exp (-(N : ℝ) ^ 2 / 2) := by
  let E : Set (Fin (N + 1) → ℝ) := {g | ∃ z : ℂ,
    ‖z‖ ≤ 1 + (K + 1) / N ∧ DerivativeSupremum.secondDerivativeEnvelope N K <
      ‖(gaussianPolynomial N g).derivative.derivative.eval z‖}
  have ht := circularGaussian_coefficient_event_le (N + 1)
    {a | ∃ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N ∧
      2 * DerivativeSupremum.secondDerivativeEnvelope N K <
        ‖(Polynomial.ofFn (N + 1) a).derivative.derivative.eval z‖} E E (by
    intro g hg
    obtain ⟨z, hz, hlarge⟩ := hg
    by_contra h
    push Not at h
    have hleft := le_of_not_gt (fun hgt => h.1 ⟨z, hz, hgt⟩)
    have hright := le_of_not_gt (fun hgt => h.2 ⟨z, hz, hgt⟩)
    have hsum := circularGaussian_second_derivative_norm_le N g z
    linarith)
  have hp := gaussian_second_derivative_supremum N hN hK hKN
  exact ht.trans ((add_le_add hp hp).trans_eq (by ring))

/-- An appended circular Gaussian tail splits into the two appended real tails. -/
theorem circularGaussian_appended_tail_eval (N M m : ℕ)
    (g : (Fin (N + M + 1) → ℝ) × (Fin (N + M + 1) → ℝ)) (z : ℂ) :
    (BoundedTailSupremum.appendedTailPolynomial N M m
      (circularGaussianCoefficientVectorEquiv (N + M + 1) g)).eval z =
      ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * (gaussianAppendedTailPolynomial N M m g.1).eval z +
      (Complex.I / (Real.sqrt 2 : ℂ)) * (gaussianAppendedTailPolynomial N M m g.2).eval z := by
  rw [BoundedTailSupremum.appendedTailPolynomial_eval,
    gaussianAppendedTailPolynomial_eval, gaussianAppendedTailPolynomial_eval]
  simp only [complexGaussianSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [circularGaussianCoefficientVectorEquiv_apply]
  ring

/-- Every partial appended tail obeys the uniform complex amplitude bound. -/
theorem circularGaussian_appended_tail_supremum (N M : ℕ) (hN : 4 ≤ N)
    (hM0 : 1 ≤ M) (hM : M ≤ N) {K : ℝ} (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ)) :
    (Measure.pi (fun _ : Fin (N + M + 1) => circularComplexGaussian)).real {a |
      ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ, ‖z‖ ≤ 1 + K / N ∧
        2 * TailSupremum.tailAmplitude N M K ≤
          ‖(BoundedTailSupremum.appendedTailPolynomial N M m a).eval z‖} ≤
      2 / (N : ℝ) ^ 10 + 4 * (N + M + 1) * Real.exp (-(N : ℝ) ^ 2 / 2) := by
  let E : Set (Fin (N + M + 1) → ℝ) := {g | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ,
    ‖z‖ ≤ 1 + K / N ∧ TailSupremum.tailAmplitude N M K ≤
      ‖(gaussianAppendedTailPolynomial N M m g).eval z‖}
  have ht := circularGaussian_coefficient_event_le (N + M + 1)
    {a | ∃ m : ℕ, m ≤ M ∧ ∃ z : ℂ, ‖z‖ ≤ 1 + K / N ∧
      2 * TailSupremum.tailAmplitude N M K ≤
        ‖(BoundedTailSupremum.appendedTailPolynomial N M m a).eval z‖} E E (by
    intro g hg
    obtain ⟨m, hm, z, hz, hlarge⟩ := hg
    by_contra h
    push Not at h
    have hleft := lt_of_not_ge (fun hgt => h.1 ⟨m, hm, z, hz, hgt⟩)
    have hright := lt_of_not_ge (fun hgt => h.2 ⟨m, hm, z, hz, hgt⟩)
    rw [circularGaussian_appended_tail_eval] at hlarge
    have hsum := norm_circular_assembly_le
      ((gaussianAppendedTailPolynomial N M m g.1).eval z)
      ((gaussianAppendedTailPolynomial N M m g.2).eval z)
    linarith)
  have hp := gaussian_appended_tail_supremum N M hN hM0 hM hK hKN
  exact ht.trans ((add_le_add hp hp).trans_eq (by ring))

end Erdos522

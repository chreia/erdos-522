/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.ShiftMultipliers
import Erdos522.Analysis.PolynomialArcRemez

/-!
# Polynomials associated with small Fourier shifts

A unit relation among shifts determines a polynomial with unit coefficient
energy. Parseval supplies a point of modulus at least one; interpolation then
forces a quantitative lower bound on every circular arc.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522.LogMoments

/-- A Fourier character turns a repeated angular shift into a power. -/
theorem fourier_nsmul_eq_pow (k j : ℕ) (t : AddCircle (1 : ℝ)) :
    fourier k (j • t) = (fourier k t)^j := by
  simp only [fourier_apply, Nat.cast_smul_eq_nsmul]
  rw [smul_comm k j, AddCircle.toCircle_nsmul, Circle.coe_pow]

/-- The shift multiplier is evaluation of the relation polynomial. -/
theorem shiftMultiplier_eq_polynomial_eval {n : ℕ} (c : Fin (n+1) → ℂ) (t : AddCircle (1 : ℝ)) (k : ℕ) :
    shiftMultiplier c t k = (Polynomial.ofFn (n+1) c).eval (fourier k t) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [shiftMultiplier, eval_monomial]
  simp only [fourier_nsmul_eq_pow]

/-- Unit coefficient energy forces modulus at least one somewhere on the circle. -/
theorem exists_unitCircle_polynomial_norm_ge_one {n : ℕ} (c : Fin (n+1) → ℂ) (hc : ∑ j, ‖c j‖^2=1) :
    ∃ z : ℂ, ‖z‖=1 ∧ 1≤‖(Polynomial.ofFn (n+1) c).eval z‖ := by
  let f := fourierPolynomial c (fun _ => true)
  have hf : Continuous f := continuous_fourierPolynomial c _
  obtain ⟨θ, -, hθ⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
  refine ⟨AddCircle.toCircle θ, Circle.norm_coe _, ?_⟩
  have heq : signedPolynomial c (fun _ => true) = Polynomial.ofFn (n+1) c := by
    rw [signedPolynomial_eq_ofFn]
    simp [sign]
  change 1 ≤ ‖(Polynomial.ofFn (n+1) c).eval (AddCircle.toCircle θ : ℂ)‖
  rw [← heq]
  change 1 ≤ ‖f θ‖
  have hle : (∫ x, ‖f x‖^2 ∂AddCircle.haarAddCircle) ≤ ‖f θ‖^2 := by
    calc
      _ ≤ ∫ _, ‖f θ‖^2 ∂(AddCircle.haarAddCircle (T := (1 : ℝ))) := by
        apply integral_mono ((hf.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
        intro x
        exact pow_le_pow_left₀ (norm_nonneg _) (hθ (Set.mem_univ x)) 2
      _ = _ := by simp
  rw [integral_norm_sq_fourierPolynomial, hc] at hle
  nlinarith [norm_nonneg (f θ)]

/-- The polynomial of a normalized shift relation cannot be uniformly too small
on an arc of positive normalized length. -/
theorem normalized_polynomial_arc_lower_bound {n : ℕ} (c : Fin (n + 1) → ℂ)
    (hc : ∑ j, ‖c j‖ ^ 2 = 1) {θ ℓ ε : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (harc : ∀ t ∈ Set.Icc θ (θ + 2 * Real.pi * ℓ),
      ‖(Polynomial.ofFn (n + 1) c).eval (unitCirclePoint t)‖ ≤ ε) :
    (ℓ / (2 * Real.exp 1)) ^ n ≤ ε := by
  obtain ⟨z, hz, hlarge⟩ := exists_unitCircle_polynomial_norm_ge_one c hc
  exact polynomial_arc_lower_bound _
    (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) c)) hℓ hℓ1 harc hz hlarge

end Erdos522.LogMoments

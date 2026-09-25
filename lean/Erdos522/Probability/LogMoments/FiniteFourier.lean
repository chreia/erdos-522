/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# Finite Rademacher Fourier polynomials

The coefficient normalization is independent of the number of terms and of the signs.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace Erdos522
namespace LogMoments

abbrev SignVector (N : ℕ) := Fin (N + 1) → Bool

def sign (b : Bool) : ℂ := if b then 1 else -1

@[simp] theorem norm_sign (b : Bool) : ‖sign b‖ = 1 := by
  cases b <;> simp [sign]

@[simp] theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by
  cases b <;> simp [sign]

def normalizedCoefficients {N : ℕ} (a : Fin (N + 1) → ℂ) (k : Fin (N + 1)) : ℂ :=
  a k / (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ)

theorem sum_sq_norm_pos {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := ha
  exact Finset.sum_pos' (fun j _ => sq_nonneg ‖a j‖)
    ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) _⟩

theorem sum_sq_norm_normalizedCoefficients {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∃ k, a k ≠ 0) : ∑ k, ‖normalizedCoefficients a k‖ ^ 2 = 1 := by
  have hs := sum_sq_norm_pos a ha
  simp only [normalizedCoefficients, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hs.le]
  rw [← Finset.sum_div, div_self hs.ne']

def signedPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ) (ω : SignVector N) : ℂ[X] :=
  ∑ k, monomial k.val (sign (ω k) * a k)

theorem signedPolynomial_eq_ofFn {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    signedPolynomial a ω = Polynomial.ofFn (N + 1) (fun k => sign (ω k) * a k) := by
  classical
  exact (Polynomial.ofFn_eq_sum_monomial _).symm

theorem degree_signedPolynomial_lt {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) : (signedPolynomial a ω).degree < (N + 1 : ℕ) := by
  classical
  rw [signedPolynomial_eq_ofFn]
  exact Polynomial.ofFn_degree_lt _

@[simp] theorem coeff_signedPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (k : Fin (N + 1)) :
    (signedPolynomial a ω).coeff k.val = sign (ω k) * a k := by
  classical
  simp only [signedPolynomial, finsetSum_coeff, coeff_monomial, Fin.val_inj]
  simp

theorem sum_sq_norm_signed {N : ℕ} (a : Fin (N + 1) → ℂ) (ω : SignVector N) :
    (∑ k, ‖sign (ω k) * a k‖ ^ 2) = ∑ k, ‖a k‖ ^ 2 := by
  simp

theorem sum_sq_norm_coeff_signedPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    (∑ k ∈ (signedPolynomial a ω).support, ‖(signedPolynomial a ω).coeff k‖ ^ 2) =
      ∑ k, ‖a k‖ ^ 2 := by
  classical
  have h := Polynomial.sum_fin (fun _ (z : ℂ) => ‖z‖ ^ 2) (by simp)
    (degree_signedPolynomial_lt a ω)
  simpa only [Polynomial.sum_def, coeff_signedPolynomial, norm_mul, norm_sign, one_mul]
    using h.symm

theorem circleAverage_norm_sq_signedPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    Real.circleAverage (fun z => ‖(signedPolynomial a ω).eval z‖ ^ 2) 0 1 =
      ∑ k, ‖a k‖ ^ 2 := by
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage, sum_sq_norm_coeff_signedPolynomial]

theorem signedPolynomial_ne_zero {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) (ω : SignVector N) : signedPolynomial a ω ≠ 0 := by
  intro h
  have hz : ∀ k, a k = 0 := by
    intro k
    have hk := congrArg (fun p : ℂ[X] => p.coeff k.val) h
    simpa using hk
  simp [hz] at ha

def fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ) (ω : SignVector N)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  (signedPolynomial a ω).eval (AddCircle.toCircle θ)

theorem finite_zero_set {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) (ω : SignVector N) :
    Set.Finite {θ : AddCircle (1 : ℝ) | fourierPolynomial a ω θ = 0} := by
  have hi : Function.Injective (fun θ : AddCircle (1 : ℝ) =>
      (AddCircle.toCircle θ : ℂ)) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  exact (Polynomial.finite_setOfPred_isRoot (signedPolynomial_ne_zero a ha ω)).preimage hi.injOn

theorem fourierPolynomial_ae_ne_zero {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∑ k, ‖a k‖ ^ 2 = 1) (ω : SignVector N) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle, fourierPolynomial a ω θ ≠ 0 := by
  rw [ae_iff]
  have hv : AddCircle.haarAddCircle (T := (1 : ℝ)) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  rw [hv]
  have : NullSingletonClass (volume : Measure (AddCircle (1 : ℝ))) := by
    constructor
    intro θ
    simpa using (AddCircle.volume_closedBall (1 : ℝ) (x := θ) (0 : ℝ))
  simpa only [not_not] using
    (finite_zero_set a ha ω).measure_zero volume

theorem signedPolynomial_circleIntegrable_log_norm {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ω : SignVector N) :
    CircleIntegrable (fun z => Real.log ‖(signedPolynomial a ω).eval z‖) 0 1 := by
  exact (analyticOnNhd_id.aeval_polynomial (signedPolynomial a ω)).meromorphicOn.circleIntegrable_log_norm

theorem fourierPolynomial_eq_sum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial a ω θ = ∑ k, sign (ω k) * a k * fourier k.val θ := by
  simp [fourierPolynomial, signedPolynomial, eval_finsetSum,
    fourier_apply, AddCircle.toCircle_nsmul]

theorem continuous_fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) : Continuous (fourierPolynomial a ω) := by
  change Continuous (fun θ => fourierPolynomial a ω θ)
  simp only [fourierPolynomial_eq_sum]
  fun_prop

theorem integrable_log_norm_fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    Integrable (fun θ => Real.log ‖fourierPolynomial a ω θ‖) AddCircle.haarAddCircle := by
  have hv : AddCircle.haarAddCircle (T := (1 : ℝ)) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  rw [hv]
  have hm : AEStronglyMeasurable (fun θ => Real.log ‖fourierPolynomial a ω θ‖)
      (volume : Measure (AddCircle (1 : ℝ))) :=
    (continuous_fourierPolynomial a ω).measurable.norm.log.aestronglyMeasurable
  apply ((UnitAddCircle.measurePreserving_mk 0).integrable_comp hm).mp
  have hi := (signedPolynomial a ω).intervalIntegrable_mahlerMeasure.comp_mul_right
    (c := 2 * Real.pi)
  have heq : ∀ t : ℝ, fourierPolynomial a ω (t : AddCircle (1 : ℝ)) =
      (signedPolynomial a ω).eval (circleMap 0 1 (t * (2 * Real.pi))) := by
    intro t
    simp only [fourierPolynomial, AddCircle.toCircle, Function.Periodic.lift_coe,
      Circle.coe_exp, circleMap, Complex.ofReal_one, one_mul, zero_add]
    congr 2
    push_cast
    ring
  simpa only [IntegrableOn, Function.comp_def, heq, zero_div, div_self Real.two_pi_pos.ne',
    zero_add] using hi.1

theorem integral_unitCircle_eq_circleAverage (f : ℂ → ℝ) :
    (∫ θ : AddCircle (1 : ℝ), f (AddCircle.toCircle θ) ∂AddCircle.haarAddCircle) =
      Real.circleAverage f 0 1 := by
  have hv : AddCircle.haarAddCircle (T := (1 : ℝ)) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  rw [hv, ← AddCircle.intervalIntegral_preimage 1 0]
  have heq : ∀ t : ℝ, (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) =
      circleMap 0 1 (t * (2 * Real.pi)) := by
    intro t
    simp only [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp,
      circleMap, Complex.ofReal_one, one_mul, zero_add]
    congr 1
    push_cast
    ring
  simp only [heq, zero_add, Real.circleAverage_def]
  simpa only [zero_mul, one_mul] using
    intervalIntegral.integral_comp_mul_right (fun t => f (circleMap 0 1 t))
      (a := 0) (b := 1) Real.two_pi_pos.ne'

theorem integral_norm_sq_fourierPolynomial {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) :
    (∫ θ, ‖fourierPolynomial a ω θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ k, ‖a k‖ ^ 2 := by
  exact (integral_unitCircle_eq_circleAverage
    (fun z => ‖(signedPolynomial a ω).eval z‖ ^ 2)).trans
      (circleAverage_norm_sq_signedPolynomial a ω)

end LogMoments
end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.Rademacher
import Erdos522.Probability.Covariance.JetEvaluation

/-!
# Exactly normalized polynomial values

The variance sum gives the exact normalization of a polynomial value.
The oscillatory part of its real covariance is a single doubled-angle kernel.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace Erdos522

/-- The exact variance of a Rademacher polynomial value at modulus `r`. -/
def radialVariance (N : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), r ^ (2 * k)

/-- The standard deviation at modulus `r`. -/
def radialSigma (N : ℕ) (r : ℝ) : ℝ := Real.sqrt (radialVariance N r)

/-- The constant coefficient gives a unit lower bound for every radial variance. -/
theorem one_le_radialVariance (N : ℕ) (r : ℝ) : 1 ≤ radialVariance N r := by
  have h := Finset.single_le_sum
    (s := Finset.range (N + 1)) (f := fun k => r ^ (2 * k))
    (fun k _ => by rw [pow_mul]; positivity) (by simp : 0 ∈ Finset.range (N + 1))
  simpa [radialVariance] using h

theorem radialVariance_pos (N : ℕ) (r : ℝ) : 0 < radialVariance N r :=
  lt_of_lt_of_le (by norm_num) (one_le_radialVariance N r)

theorem radialSigma_pos (N : ℕ) (r : ℝ) : 0 < radialSigma N r :=
  Real.sqrt_pos.mpr (radialVariance_pos N r)

theorem radialSigma_sq (N : ℕ) (r : ℝ) : radialSigma N r ^ 2 = radialVariance N r :=
  Real.sq_sqrt (radialVariance_pos N r).le

/-- The real coefficient vector for an exactly normalized complex polynomial value. -/
def realValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![r ^ k.val / radialSigma N r * (z ^ k.val).re,
    r ^ k.val / radialSigma N r * (z ^ k.val).im]

/-- The real coordinates of the random polynomial value divided by its exact standard deviation. -/
def realRademacherValue (N : ℕ) (r : ℝ) (z : ℂ) :
    LogMoments.SignVector N → EuclideanSpace ℝ (Fin 2) :=
  signVectorSum (realValueCoefficient N r z)

/-- A real direction is the real part of a complex projection. -/
theorem inner_realValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1))
    (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, realValueCoefficient N r z k⟫ =
      (r ^ k.val / radialSigma N r) * ((⟨x 0, -x 1⟩ : ℂ) * z ^ k.val).re := by
  simp only [realValueCoefficient, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.mul_re]
  ring

/-- The exact normalization rescales the value part of the jet covariance. -/
theorem quadratic_realValueCoefficient_eq_jet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x.ofLp ⬝ᵥ signCovarianceMatrix (realValueCoefficient N r z) *ᵥ x.ofLp =
      ((N : ℝ) / radialVariance N r) * jetCovarianceForm N r z ⟨x 0, -x 1⟩ 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [signCovarianceMatrix_form]
  simp_rw [← pow_two, inner_realValueCoefficient, mul_pow, div_pow, radialSigma_sq]
  unfold jetCovarianceForm
  simp only [mul_zero, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← pow_mul, mul_comm k.val 2]
  field_simp

/-- The complex direction parametrization preserves its two-dimensional Euclidean norm. -/
theorem value_direction_norm (x : EuclideanSpace ℝ (Fin 2)) :
    ‖(⟨x 0, -x 1⟩ : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_mk]
  ring

/-- The covariance decomposes into one half of the identity and one oscillatory kernel. -/
theorem quadratic_realValueCoefficient_decomposition (N : ℕ) (hN : 0 < N) (r : ℝ)
    (z : ℂ) (hz : ‖z‖ = 1) (x : EuclideanSpace ℝ (Fin 2)) :
    2 * (x.ofLp ⬝ᵥ signCovarianceMatrix (realValueCoefficient N r z) *ᵥ x.ofLp) =
      ‖x‖ ^ 2 + ((N : ℝ) / radialVariance N r) *
        (((⟨x 0, -x 1⟩ : ℂ) ^ 2) * radialIndexKernel N 0 r (z ^ 2)).re := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hv := (radialVariance_pos N r).ne'
  have h := jetCovarianceForm_decomposition N r z ⟨x 0, -x 1⟩ 0 hz
  simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    value_direction_norm, ← Finset.sum_mul] at h
  change 2 * jetCovarianceForm N r z ⟨x 0, -x 1⟩ 0 =
    (1 / (N : ℝ)) * (radialVariance N r * ‖x‖ ^ 2) + _ at h
  rw [quadratic_realValueCoefficient_eq_jet N hN]
  calc
    _ = ((N : ℝ) / radialVariance N r) * (2 * jetCovarianceForm N r z ⟨x 0, -x 1⟩ 0) := by ring
    _ = _ := by rw [h]; field_simp

/-- The variance normalization changes an `N`-normalized form by at most `exp(4K)`. -/
theorem degree_div_radialVariance_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N) :
    (N : ℝ) / radialVariance N r ≤ Real.exp (4 * K) := by
  have hlow := (radial_variance_bounds N hN K r hK hNK hrl hru).1
  have hexp : Real.exp (-4 * K) * Real.exp (4 * K) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  apply (div_le_iff₀ (radialVariance_pos N r)).mpr
  have h := mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg (4 * K))
  change (N : ℝ) * Real.exp (-4 * K) * Real.exp (4 * K) ≤
    radialVariance N r * Real.exp (4 * K) at h
  calc
    (N : ℝ) = ((N : ℝ) * Real.exp (-4 * K)) * Real.exp (4 * K) := by
      rw [mul_assoc, hexp, mul_one]
    _ ≤ _ := h
    _ = _ := mul_comm _ _

/-- A radial kernel at inverse-square-root angular separation has that same decay. -/
theorem radialIndexKernel_bound_sqrt (N j : ℕ) (hN : 0 < N) (K r t : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r ≤ 1 + K / N)
    (hangle : 1 / Real.sqrt N ≤ ‖(t : Real.Angle)‖) :
    ‖radialIndexKernel N j r (Complex.exp (Complex.I * t))‖ ≤
      10 * Real.exp (4 * K) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsep := degree_times_separation_lower N hN (Real.sqrt N) ‖(t : Real.Angle)‖
    hs.le (by rw [Real.sq_sqrt hn.le]) hangle
  have hden : 0 < (N : ℝ) * ‖(t : Real.Angle)‖ := hs.trans_le hsep
  have ht : (t : Real.Angle) ≠ 0 := by intro ht; simp [ht] at hden
  exact (radialIndexKernel_bound N j hN K r t hK hr0 hr ht).trans
    (div_le_div_of_nonneg_left (by positivity) hs hsep)

/-- The covariance of an exactly normalized value differs from the circular
covariance by at most `5 exp(8K)/sqrt N`. -/
theorem realValue_covariance_circular_error (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 2)) :
    |x.ofLp ⬝ᵥ signCovarianceMatrix (realValueCoefficient N r (Complex.exp (Complex.I * θ))) *ᵥ x.ofLp -
      (1 / 2 : ℝ) * ‖x‖ ^ 2| ≤ (5 * Real.exp (8 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hnorm := degree_div_radialVariance_le N hN K r hK hNK hrl hru
  have hkernel := radialIndexKernel_bound_sqrt N 0 hN K r (2 * θ) hK hr0 hru hangle
  rw [← phase_square θ] at hkernel
  have hproj : |(((⟨x 0, -x 1⟩ : ℂ) ^ 2) *
      radialIndexKernel N 0 r (Complex.exp (Complex.I * θ) ^ 2)).re| ≤
      ‖x‖ ^ 2 * (10 * Real.exp (4 * K) / Real.sqrt N) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, value_direction_norm]
    exact mul_le_mul_of_nonneg_left hkernel (sq_nonneg _)
  have hdecomp := quadratic_realValueCoefficient_decomposition N hN r
    (Complex.exp (Complex.I * θ)) (Complex.norm_exp_I_mul_ofReal θ) x
  have hv0 : 0 ≤ (N : ℝ) / radialVariance N r := div_nonneg hn.le (radialVariance_pos N r).le
  have herror : |2 * (x.ofLp ⬝ᵥ signCovarianceMatrix
      (realValueCoefficient N r (Complex.exp (Complex.I * θ))) *ᵥ x.ofLp) - ‖x‖ ^ 2| ≤
      (10 * Real.exp (8 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
    rw [hdecomp, add_sub_cancel_left, abs_mul, abs_of_nonneg hv0]
    calc
      _ ≤ Real.exp (4 * K) * (‖x‖ ^ 2 * (10 * Real.exp (4 * K) / Real.sqrt N)) :=
        mul_le_mul hnorm hproj (abs_nonneg _) (Real.exp_nonneg _)
      _ = _ := by
        have he : Real.exp (4 * K) * Real.exp (4 * K) = Real.exp (8 * K) := by
          rw [← Real.exp_add]; congr 1; ring
        calc
          _ = 10 * (Real.exp (4 * K) * Real.exp (4 * K)) / Real.sqrt N * ‖x‖ ^ 2 := by ring
          _ = _ := by rw [he]
  rcases abs_le.mp herror with ⟨hl, hu⟩
  have hscale : (10 * Real.exp (8 * K) / Real.sqrt N) * ‖x‖ ^ 2 =
      2 * ((5 * Real.exp (8 * K) / Real.sqrt N) * ‖x‖ ^ 2) := by ring
  rw [hscale] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The squared size of an exactly normalized value coefficient. -/
theorem norm_sq_realValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (k : Fin (N + 1)) :
    ‖realValueCoefficient N r z k‖ ^ 2 = r ^ (2 * k.val) / radialVariance N r := by
  have hphase : (z ^ k.val).re ^ 2 + (z ^ k.val).im ^ 2 = 1 := by
    calc
      _ = ‖z ^ k.val‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by simp [norm_pow, hz]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [realValueCoefficient, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_pow, div_pow, radialSigma_sq]
  rw [show 2 * k.val = k.val * 2 by omega, pow_mul]
  nlinarith [congrArg (fun t : ℝ => (r ^ k.val) ^ 2 / radialVariance N r * t) hphase]

/-- Exact normalization gives total coefficient energy one. -/
theorem sum_sq_norm_realValueCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ k, ‖realValueCoefficient N r z k‖ ^ 2 = 1 := by
  simp_rw [norm_sq_realValueCoefficient N r z hz]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => r ^ (2 * k)) (N + 1)]
  exact div_self (radialVariance_pos N r).ne'

/-- Every normalized value coefficient has size at most `exp(3K)/sqrt N` in the annulus. -/
theorem norm_realValueCoefficient_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) (k : Fin (N + 1)) :
    ‖realValueCoefficient N r z k‖ ≤ Real.exp (3 * K) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hrad := radial_power_upper N k.val hN (by omega) K r hK hr0 hru
  have hrad₂ : r ^ (2 * k.val) ≤ Real.exp (2 * K) := by
    rw [show 2 * k.val = k.val * 2 by omega, pow_mul]
    have he : Real.exp K ^ 2 = Real.exp (2 * K) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [← he]
    nlinarith [pow_nonneg hr0 k.val, Real.exp_pos K]
  have hnorm := degree_div_radialVariance_le N hN K r hK hNK hrl hru
  have he : Real.exp (2 * K) * Real.exp (4 * K) = Real.exp (6 * K) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : ‖realValueCoefficient N r z k‖ ^ 2 ≤ Real.exp (6 * K) / N := by
    rw [norm_sq_realValueCoefficient N r z hz k]
    calc
      _ = (r ^ (2 * k.val) / N) * ((N : ℝ) / radialVariance N r) := by field_simp
      _ ≤ (Real.exp (2 * K) / N) * Real.exp (4 * K) :=
        mul_le_mul (div_le_div_of_nonneg_right hrad₂ hn.le) hnorm
          (div_nonneg hn.le (radialVariance_pos N r).le) (by positivity)
      _ = _ := by rw [div_mul_eq_mul_div, he]
  have hmax : (Real.exp (3 * K) / Real.sqrt N) ^ 2 = Real.exp (6 * K) / N := by
    rw [div_pow, Real.sq_sqrt hn.le, pow_two, ← Real.exp_add]
    congr 2
    ring
  rw [← hmax] at hsq
  nlinarith [norm_nonneg (realValueCoefficient N r z k),
    div_pos (Real.exp_pos (3 * K)) hs]

/-- Unit coefficient energy and a coefficient supremum give the exact third-moment scale. -/
theorem sum_third_norm_realValueCoefficient_le (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ k, ‖realValueCoefficient N r z k‖ ^ 3) ≤ Real.exp (3 * K) / Real.sqrt N := by
  calc
    _ ≤ ∑ k, (Real.exp (3 * K) / Real.sqrt N) * ‖realValueCoefficient N r z k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_realValueCoefficient_le N hN K r hK hNK hrl hru z hz k) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, sum_sq_norm_realValueCoefficient N r z hz, mul_one]

/-- The normalized real value vector is precisely the polynomial value divided by `σ_N(r)`. -/
theorem realRademacherValue_eq_polynomial (N : ℕ) (r : ℝ) (z : ℂ)
    (ω : LogMoments.SignVector N) :
    realRademacherValue N r z ω = toLp 2 ![
      ((rademacherPolynomial N ω).eval (r * z)).re / radialSigma N r,
      ((rademacherPolynomial N ω).eval (r * z)).im / radialSigma N r] := by
  ext i
  fin_cases i <;>
    simp only [realRademacherValue, signVectorSum, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, realValueCoefficient, rademacherPolynomial_eval,
      Complex.re_sum, Complex.im_sum, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    simp only [← LogMoments.ofReal_realSign, mul_pow, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    norm_num
    ring

end Erdos522

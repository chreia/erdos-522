/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.Khintchine

/-!
# Moments of quadratic Rademacher sums

Deleting the diagonal leaves a quadratic sign sum with mean zero. The
Hanson–Wright exponential estimate at the Frobenius scale controls its moments
uniformly in the matrix dimension.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- The Euclidean operator norm is bounded by the Frobenius norm. -/
theorem operatorNorm_le_frobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    HansonWright.operatorNorm A ≤ HansonWright.frobeniusNorm A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (HansonWright.frobeniusNorm_nonneg A)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (HansonWright.frobeniusNorm_nonneg A) (norm_nonneg x))).mp
  rw [mul_pow, HansonWright.frobeniusNorm_sq]
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hx, Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, x.ofLp j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x.ofLp
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The off-diagonal real quadratic sign sum. -/
def quadraticSignSum {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (ω : SignVector N) : ℝ :=
  HansonWright.quadraticForm (HansonWright.offDiagonalMatrix A)
    (fun k => realSign (ω k))

/-- The off-diagonal exponential moment on a dimension-independent interval. -/
theorem integral_exp_quadraticSignSum_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    {V t : ℝ} (hV : 0 < V) (hA : HansonWright.frobeniusNorm A ≤ V)
    (ht : t ^ 2 * (4 * Real.exp 1 * V) ^ 2 ≤ 1) :
    (∫ ω, Real.exp (t * quadraticSignSum A ω) ∂signMeasure N) ≤ Real.exp 1 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hF : 0 ≤ HansonWright.frobeniusNorm A := HansonWright.frobeniusNorm_nonneg A
  have hop : 0 ≤ HansonWright.operatorNorm A := norm_nonneg _
  have hsmall :
      (1 ^ 2 * (4 * t) ^ 2 / 2) * 1 ^ 2 * HansonWright.operatorNorm A ^ 2 *
        Real.exp 1 ≤ 1 / 2 := by
    calc
      _ = (4 * t) ^ 2 * HansonWright.operatorNorm A ^ 2 * Real.exp 1 / 2 := by ring
      _ ≤ (4 * t) ^ 2 * V ^ 2 * Real.exp 1 ^ 2 / 2 := by
        gcongr
        · exact (operatorNorm_le_frobeniusNorm A).trans hA
        · nlinarith [Real.exp_pos 1]
      _ = t ^ 2 * (4 * Real.exp 1 * V) ^ 2 / 2 := by ring
      _ ≤ 1 / 2 := by linarith
  have h := HansonWright.integral_exp_quadraticForm_offDiagonal_le
    (K := 1) (l := t) A (iIndepFun_realSign N)
    (fun k => by
      convert! hasSubgaussianMGF_coordinate k using 1
      congr 1
      change NNReal.mk ((1 : ℝ) ^ 2) _ = 1
      norm_num) hsmall
  apply h.trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.exp 1 ^ 2 * (4 * t) ^ 2 * 1 ^ 4 * V ^ 2 := by gcongr
    _ = t ^ 2 * (4 * Real.exp 1 * V) ^ 2 := by ring
    _ ≤ 1 := ht

/-- An explicit even-moment bound for a real quadratic Rademacher sum. -/
theorem integral_even_pow_quadraticSignSum_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    {V : ℝ} (hV : 0 < V) (hA : HansonWright.frobeniusNorm A ≤ V) (m : ℕ) :
    (∫ ω, quadraticSignSum A ω ^ (2 * m) ∂signMeasure N) ≤
      (Nat.factorial (2 * m) : ℝ) * (4 * Real.exp 1 * V) ^ (2 * m) * Real.exp 1 := by
  let s : ℝ := (4 * Real.exp 1 * V)⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have hscale : s ^ 2 * (4 * Real.exp 1 * V) ^ 2 = 1 := by
    dsimp [s]
    field_simp
  have hpos := integral_exp_quadraticSignSum_le A hV hA hscale.le
  have hneg := integral_exp_quadraticSignSum_le A hV hA
    (t := -s) (by simpa only [neg_sq] using hscale.le)
  have hcosh : (∫ ω, Real.cosh (s * quadraticSignSum A ω) ∂signMeasure N) ≤ Real.exp 1 := by
    simp_rw [Real.cosh_eq]
    rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]
    have hneg' : (∫ ω, Real.exp (-(s * quadraticSignSum A ω)) ∂signMeasure N) ≤ Real.exp 1 := by
      simpa only [neg_mul] using hneg
    linarith
  have hterm : (∫ ω, (s * quadraticSignSum A ω) ^ (2 * m) /
      (Nat.factorial (2 * m) : ℝ) ∂signMeasure N) ≤ Real.exp 1 :=
    (integral_mono Integrable.of_finite Integrable.of_finite
      (fun ω => HansonWright.cosh_taylor_term_le (s * quadraticSignSum A ω) m)).trans hcosh
  simp_rw [mul_pow] at hterm
  rw [integral_div, integral_const_mul] at hterm
  have hf : (0 : ℝ) < Nat.factorial (2 * m) := by positivity
  have hbound := (div_le_iff₀ hf).mp hterm
  have hbound' : (∫ ω, quadraticSignSum A ω ^ (2 * m) ∂signMeasure N) ≤
      (Real.exp 1 * (Nat.factorial (2 * m) : ℝ)) / s ^ (2 * m) := by
    apply (le_div_iff₀ (pow_pos hs _)).mpr
    nlinarith [hbound]
  apply hbound'.trans_eq
  dsimp [s]
  rw [inv_pow, div_inv_eq_mul]
  ring

/-- Complex quadratic signs with the diagonal omitted. -/
def complexQuadraticSignSum {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (ω : SignVector N) : ℂ :=
  ∑ i, ∑ j, (if i = j then 0 else A i j) * sign (ω i) * sign (ω j)

@[simp] theorem re_complexQuadraticSignSum {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (ω : SignVector N) :
    (complexQuadraticSignSum A ω).re = quadraticSignSum (fun i j => (A i j).re) ω := by
  simp only [complexQuadraticSignSum, quadraticSignSum, HansonWright.quadraticForm,
    HansonWright.offDiagonalMatrix, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [← ofReal_realSign, Complex.mul_re, Complex.mul_im]

@[simp] theorem im_complexQuadraticSignSum {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (ω : SignVector N) :
    (complexQuadraticSignSum A ω).im = quadraticSignSum (fun i j => (A i j).im) ω := by
  simp only [complexQuadraticSignSum, quadraticSignSum, HansonWright.quadraticForm,
    HansonWright.offDiagonalMatrix, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [← ofReal_realSign, Complex.mul_re, Complex.mul_im]

/-- A complex bilinear moment bound with the total coefficient energy. -/
theorem integral_even_norm_complexQuadraticSignSum_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {V : ℝ} (hV : 0 < V) (hA : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ V)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, ‖complexQuadraticSignSum A ω‖ ^ (2 * m) ∂signMeasure N) ≤
      2 ^ m * (Nat.factorial (2 * m) : ℝ) *
        (4 * Real.exp 1) ^ (2 * m) * V ^ m * Real.exp 1 := by
  have hreal : HansonWright.frobeniusNorm (fun i j => (A i j).re) ≤ Real.sqrt V := by
    apply Real.sqrt_le_sqrt
    apply le_trans _ hA
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (A i j).im]
  have himag : HansonWright.frobeniusNorm (fun i j => (A i j).im) ≤ Real.sqrt V := by
    apply Real.sqrt_le_sqrt
    apply le_trans _ hA
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (A i j).re]
  have hre := integral_even_pow_quadraticSignSum_le
    (fun i j => (A i j).re) (Real.sqrt_pos.mpr hV) hreal m
  have him := integral_even_pow_quadraticSignSum_le
    (fun i j => (A i j).im) (Real.sqrt_pos.mpr hV) himag m
  have hpoint (ω : SignVector N) :
      ‖complexQuadraticSignSum A ω‖ ^ (2 * m) ≤ 2 ^ (m - 1) *
        ((complexQuadraticSignSum A ω).re ^ (2 * m) +
          (complexQuadraticSignSum A ω).im ^ (2 * m)) := by
    rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
    simpa only [pow_mul, pow_two] using
      add_pow_le (sq_nonneg (complexQuadraticSignSum A ω).re)
        (sq_nonneg (complexQuadraticSignSum A ω).im) m
  have htwo : (2 : ℝ) ^ (m - 1) * 2 = 2 ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  calc
    _ ≤ ∫ ω, 2 ^ (m - 1) *
        ((complexQuadraticSignSum A ω).re ^ (2 * m) +
          (complexQuadraticSignSum A ω).im ^ (2 * m)) ∂signMeasure N :=
      integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = 2 ^ (m - 1) *
        ((∫ ω, quadraticSignSum (fun i j => (A i j).re) ω ^ (2 * m) ∂signMeasure N) +
          ∫ ω, quadraticSignSum (fun i j => (A i j).im) ω ^ (2 * m) ∂signMeasure N) := by
      rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite]
      simp only [re_complexQuadraticSignSum, im_complexQuadraticSignSum]
    _ ≤ 2 ^ (m - 1) * (2 * ((Nat.factorial (2 * m) : ℝ) *
        (4 * Real.exp 1 * Real.sqrt V) ^ (2 * m) * Real.exp 1)) := by
      gcongr
      linarith
    _ = _ := by
      rw [← mul_assoc, htwo, mul_pow, pow_mul (Real.sqrt V), Real.sq_sqrt hV.le]
      ring

/-- Polynomial growth in the moment order for quadratic signs. -/
theorem integral_even_norm_complexQuadraticSignSum_le_pow {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {V : ℝ} (hV : 0 < V) (hA : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ V)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, ‖complexQuadraticSignSum A ω‖ ^ (2 * m) ∂signMeasure N) ≤
      (16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m := by
  have hf : (Nat.factorial (2 * m) : ℝ) ≤ (2 * (m : ℝ)) ^ (2 * m) := by
    exact_mod_cast Nat.factorial_le_pow (2 * m)
  have ht : (2 : ℝ) ^ m ≤ 2 ^ (2 * m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have he : Real.exp 1 ≤ Real.exp 1 ^ (2 * m) := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
        (by omega : 1 ≤ 2 * m)
  calc
    _ ≤ 2 ^ m * (Nat.factorial (2 * m) : ℝ) *
        (4 * Real.exp 1) ^ (2 * m) * V ^ m * Real.exp 1 :=
      integral_even_norm_complexQuadraticSignSum_le A hV hA m hm
    _ ≤ 2 ^ (2 * m) * (2 * (m : ℝ)) ^ (2 * m) *
        (4 * Real.exp 1) ^ (2 * m) * V ^ m * Real.exp 1 ^ (2 * m) := by gcongr
    _ = _ := by
      have hc : 2 * (2 * (m : ℝ)) * (4 * Real.exp 1) * Real.exp 1 =
          16 * Real.exp 2 * (m : ℝ) := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        ring
      rw [← hc]
      simp only [mul_pow]
      ring

/-- The bilinear Khintchine inequality depends only on the off-diagonal
    coefficient energy. -/
theorem integral_even_norm_offDiagonalSignSum_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {V : ℝ} (hV : 0 < V)
    (hA : ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖ ^ 2) ≤ V)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, ‖complexQuadraticSignSum A ω‖ ^ (2 * m) ∂signMeasure N) ≤
      (16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    fun i j => if i = j then 0 else A i j
  have henergy : ∑ i, ∑ j, ‖B i j‖ ^ 2 =
      ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [B, hij]
  have heq : complexQuadraticSignSum B = complexQuadraticSignSum A := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [B, hij]
  have h := integral_even_norm_complexQuadraticSignSum_le_pow B hV
    (by rwa [henergy]) m hm
  rwa [heq] at h

/-- The degree-two sign Fourier sum whose frequencies are differences of indices. -/
def randomBilinearFourier {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (q : SignVector N × AddCircle (1 : ℝ)) : ℂ :=
  complexQuadraticSignSum (fun i j => A i j * fourier ((i : ℤ) - (j : ℤ)) q.2) q.1

theorem measurable_randomBilinearFourier {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Measurable (randomBilinearFourier A) := by
  unfold randomBilinearFourier complexQuadraticSignSum
  have hs (k : Fin (N + 1)) : Measurable (fun ω : SignVector N => sign (ω k)) :=
    measurable_of_finite _
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> fun_prop

theorem continuous_randomBilinearFourier_angle {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (ω : SignVector N) :
    Continuous (fun θ => randomBilinearFourier A (ω, θ)) := by
  unfold randomBilinearFourier complexQuadraticSignSum
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> fun_prop

theorem integrable_pow_norm_randomBilinearFourier {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : ℕ) :
    Integrable (fun q => ‖randomBilinearFourier A q‖ ^ p) (fourierMeasure N) := by
  apply (integrable_prod_iff
    ((measurable_randomBilinearFourier A).norm.pow_const p).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω =>
      ((continuous_randomBilinearFourier_angle A ω).norm.pow p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact Integrable.of_finite

/-- The bilinear Fourier estimate on the full sign-and-angle probability space. -/
theorem integral_even_norm_randomBilinearFourier_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {V : ℝ} (hV : 0 < V)
    (hA : ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖ ^ 2) ≤ V)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ q, ‖randomBilinearFourier A q‖ ^ (2 * m) ∂fourierMeasure N) ≤
      (16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m := by
  have hi := integrable_pow_norm_randomBilinearFourier A (2 * m)
  rw [fourierMeasure, integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _θ : AddCircle (1 : ℝ),
        (16 * Real.exp 2 * (m : ℝ)) ^ (2 * m) * V ^ m ∂AddCircle.haarAddCircle := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      intro θ
      change (∫ ω, ‖complexQuadraticSignSum
        (fun i j => A i j * fourier ((i : ℤ) - (j : ℤ)) θ) ω‖ ^ (2 * m)
          ∂signMeasure N) ≤ _
      exact integral_even_norm_offDiagonalSignSum_le _ hV
        (by simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hA) m hm
    _ = _ := by simp

end Erdos522.LogMoments

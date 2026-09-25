/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeLimits
import Erdos522.Probability.RademacherLogarithmicConcentration

/-!
# Dependence of annular constants on the width

The Gaussian approximation constants grow at most exponentially in the
annular width. The resulting derivative-count failure coefficient has an
explicit fourth-degree polynomial factor and exponential rate thirteen.
These are finite inequalities, so they remain valid at varying widths.
-/

noncomputable section
namespace Erdos522

theorem annular_covariance_sqrt_eq (K : ℝ) {b : ℝ} (_hb : 0 < b) :
    Real.sqrt (Real.exp (-4 * K) / b) = Real.exp (-2 * K) / Real.sqrt b := by
  rw [Real.sqrt_div (Real.exp_nonneg _)]
  congr 1
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg _) (Real.exp_nonneg _)).mpr
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem jetGaussianErrorConstant_eq_exp (C K : ℝ) :
    jetGaussianErrorConstant C K = jetGaussianErrorConstant C 0 * Real.exp (9 * K) := by
  unfold jetGaussianErrorConstant
  rw [annular_covariance_sqrt_eq K (by norm_num : (0 : ℝ) < 80)]
  simp only [mul_zero, Real.exp_zero, one_div, Real.sqrt_inv]
  rw [div_pow, ← Real.exp_nat_mul]
  have hexp : Real.exp (3 * K) / Real.exp ((3 : ℕ) * (-2 * K)) = Real.exp (9 * K) := by
    rw [← Real.exp_sub]
    congr 1
    norm_num
    ring
  calc
    _ = (16 * C * (4 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 80 ^ 3) *
        (Real.exp (3 * K) / Real.exp ((3 : ℕ) * (-2 * K))) := by ring_nf; simp only [inv_inv]; ring
    _ = _ := by rw [hexp]; ring_nf; simp only [inv_inv]; ring

theorem pairedJetGaussianErrorConstant_eq_exp (C K : ℝ) :
    pairedJetGaussianErrorConstant C K = pairedJetGaussianErrorConstant C 0 * Real.exp (9 * K) := by
  unfold pairedJetGaussianErrorConstant
  rw [annular_covariance_sqrt_eq K (by norm_num : (0 : ℝ) < 160)]
  simp only [mul_zero, Real.exp_zero, one_div, Real.sqrt_inv]
  rw [div_pow, ← Real.exp_nat_mul]
  have hexp : Real.exp (3 * K) / Real.exp ((3 : ℕ) * (-2 * K)) = Real.exp (9 * K) := by
    rw [← Real.exp_sub]
    congr 1
    norm_num
    ring
  calc
    _ = (128 * C * (8 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 160 ^ 3) *
        (Real.exp (3 * K) / Real.exp ((3 : ℕ) * (-2 * K))) := by ring_nf; simp only [inv_inv]; ring
    _ = _ := by rw [hexp]; ring_nf; simp only [inv_inv]; ring

theorem annular_covariance_comparison_eq (K : ℝ) :
    80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80) = 6400 * Real.exp (8 * K) := by
  calc
    _ = 6400 * (Real.exp (4 * K) / Real.exp (-4 * K)) := by ring
    _ = _ := by rw [← Real.exp_sub]; congr 2; ring

theorem annularJetPairConstant_le_exp {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K) :
    annularJetPairConstant C K ≤ annularJetPairConstant C 0 * Real.exp (9 * K) := by
  have hJ := jetGaussianErrorConstant_pos C 0 hC
  have hP := pairedJetGaussianErrorConstant_pos C 0 hC
  unfold annularJetPairConstant
  rw [jetGaussianErrorConstant_eq_exp C K, pairedJetGaussianErrorConstant_eq_exp C K,
    annular_covariance_comparison_eq K, annular_covariance_comparison_eq 0]
  have he : Real.exp (8 * K) ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  simp only [mul_zero, Real.exp_zero]
  nlinarith

theorem valueGaussianErrorConstant_pos {C : ℝ} (hC : 0 < C) (K : ℝ) :
    0 < valueGaussianErrorConstant C K := by
  unfold valueGaussianErrorConstant
  positivity

theorem valueGaussianErrorConstant_le_exp {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K) :
    valueGaussianErrorConstant C K ≤ valueGaussianErrorConstant C 0 * Real.exp (9 * K) := by
  have h₃ : Real.exp (3 * K) ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  have h₈ : Real.exp (8 * K) ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  have hc : 0 ≤ 8 * C * (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  unfold valueGaussianErrorConstant
  simp only [mul_zero, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left h₃ hc]

/-- The occupation coefficient has exponential growth rate nine with the
normalization supplied by the local Bentkus interface. -/
theorem rademacherOccupationConstant_le_exp {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K) :
    rademacherOccupationConstant C K ≤ rademacherOccupationConstant C 0 * Real.exp (9 * K) := by
  have hpositive (s : ℝ) : 0 ≤ valueGaussianErrorConstant C s + 1 / Real.pi := by
    have := valueGaussianErrorConstant_pos hC s
    positivity
  have hpositive' (s : ℝ) :
      0 ≤ valuePairGaussianErrorConstant C s + 2 * valueGaussianErrorConstant C s + 6 / Real.pi := by
    have hv := valueGaussianErrorConstant_pos hC s
    have hj := jetGaussianErrorConstant_pos C s hC
    have hp := pairedJetGaussianErrorConstant_pos C s hC
    unfold valuePairGaussianErrorConstant
    positivity
  unfold rademacherOccupationConstant
  rw [abs_of_nonneg (hpositive K), abs_of_nonneg (hpositive' K),
    abs_of_nonneg (hpositive 0), abs_of_nonneg (hpositive' 0)]
  unfold valuePairGaussianErrorConstant
  rw [jetGaussianErrorConstant_eq_exp C K, pairedJetGaussianErrorConstant_eq_exp C K,
    annular_covariance_comparison_eq K, annular_covariance_comparison_eq 0]
  simp only [mul_zero, Real.exp_zero, mul_one]
  have hv := valueGaussianErrorConstant_le_exp hC hK
  have he : 1 ≤ Real.exp (9 * K) := Real.one_le_exp_iff.mpr (by positivity)
  have h₈ : Real.exp (8 * K) ≤ Real.exp (9 * K) := Real.exp_le_exp.mpr (by linarith)
  have hpi : 0 ≤ 7 / Real.pi := by positivity
  simp only [div_eq_mul_inv] at *
  nlinarith [mul_le_mul_of_nonneg_left he hpi]

theorem annularDerivativeScale_eq_exp (K : ℝ) :
    annularDerivativeScale K = annularDerivativeScale 0 * Real.exp K := by
  unfold annularDerivativeScale
  rw [Real.exp_add]
  simp only [zero_add]
  ring

theorem annularMeshSizeConstant_eq_exp (K : ℝ) :
    annularMeshSizeConstant K (annularDerivativeScale K) =
      annularMeshSizeConstant 0 (annularDerivativeScale 0) * (K + 1) * Real.exp (2 * K) := by
  rw [annularDerivativeScale_eq_exp]
  unfold annularMeshSizeConstant
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [show (2 : ℕ) * K = (2 : ℝ) * K by norm_num]
  norm_num
  ring

theorem localCountConstant_width_le {K : ℝ} (hK : 0 ≤ K) :
    LocalZeroCount.localCountConstant (K + 2) ≤
      LocalZeroCount.localCountConstant 2 * (K + 1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold LocalZeroCount.localCountConstant
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog.le
  have hA : 0 ≤ ArcEnergy.arcScale := by unfold ArcEnergy.arcScale; positivity
  nlinarith

/-- The complete bad-root failure constant has growth `(K+1)^4 exp(13K)`. -/
theorem annularSmallDerivativeFailureConstant_le_exp {C K : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) :
    annularSmallDerivativeFailureConstant C K (K + 2) ≤
      annularSmallDerivativeFailureConstant C 0 2 * (K + 1) ^ 4 * Real.exp (13 * K) := by
  have hc0 : 0 ≤ LocalZeroCount.localCountConstant (K + 2) := by
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  have hpair := annularJetPairConstant_pos C K hC
  have hpair0 := annularJetPairConstant_pos C 0 hC
  have hV : annularJetPairConstant C K + 5 ≤
      (annularJetPairConstant C 0 + 5) * Real.exp (9 * K) := by
    have he : 1 ≤ Real.exp (9 * K) := Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [annularJetPairConstant_le_exp hC hK]
  unfold annularSmallDerivativeFailureConstant
  rw [annularMeshSizeConstant_eq_exp K]
  calc
    _ ≤ 16 * (LocalZeroCount.localCountConstant 2 * (K + 1)) ^ 2 *
        ((annularJetPairConstant C 0 + 5) * Real.exp (9 * K)) *
        (annularMeshSizeConstant 0 (annularDerivativeScale 0) * (K + 1) * Real.exp (2 * K)) ^ 2 := by
      gcongr
      exact localCountConstant_width_le hK
    _ = _ := by
      rw [show (13 : ℝ) * K = 9 * K + 2 * (2 * K) by ring,
        Real.exp_add, show Real.exp (2 * (2 * K)) = Real.exp (2 * K) ^ 2 by
          simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (2 * K) 2]
      ring

end Erdos522

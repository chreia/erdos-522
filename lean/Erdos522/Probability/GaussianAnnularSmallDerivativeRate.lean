/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianAnnularSmallDerivative
import Erdos522.Probability.AnnularSmallDerivativeLimits

/-!
# Quantitative Gaussian annular nondegeneracy

The Gaussian density and covariance terms fit the general annular mesh
majorants. The local-count coefficient is enlarged by one unit of width,
while the Gaussian energy and coefficient-truncation exceptions remain
explicit in the failure envelope.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The exact Gaussian one-point density fits the general mesh majorant. -/
theorem gaussian_pointProbability_le_annular_majorant (N : ℕ) (K u v : ℝ) :
    GaussianAnnularJetCount.pointProbabilityBound K u v ≤ annularJetProbabilityBound N 1 K u v := by
  have h := jetGaussianErrorConstant_pos 1 K (by norm_num)
  unfold GaussianAnnularJetCount.pointProbabilityBound annularJetProbabilityBound
  exact le_add_of_nonneg_right (by positivity)

/-- The Gaussian covariance comparison is a summand of the general pair coefficient. -/
theorem gaussian_pairError_le_annular_majorant (K : ℝ) :
    GaussianAnnularJetCount.pairErrorConstant K ≤ annularJetPairConstant 1 K := by
  have hj := jetGaussianErrorConstant_pos 1 K (by norm_num)
  have hp := pairedJetGaussianErrorConstant_pos 1 K (by norm_num)
  unfold GaussianAnnularJetCount.pairErrorConstant annularJetPairConstant
  linarith

/-- A unit enlargement absorbs the Gaussian local-count constant. -/
theorem gaussian_localCountConstant_le (K : ℝ) :
    GaussianLocalZeroCount.localCountConstant (K + 2) ≤ LocalZeroCount.localCountConstant (K + 3) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold GaussianLocalZeroCount.localCountConstant LocalZeroCount.localCountConstant
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hl.le
  linarith

/-- The complete Gaussian small-derivative failure envelope. -/
def gaussianAnnularDerivativeFailure (C : ℝ) (N : ℕ) : ℝ :=
  1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
    C * (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 +
    Real.exp (-3 * (N + 1 : ℝ) / 32) + 2 * (N + 1) * Real.exp (-(N : ℝ) ^ 2 / 2)

/-- Gaussian annular small-derivative roots satisfy the same count exponent,
with both additional Gaussian exceptional probabilities retained. -/
theorem eventually_gaussian_annular_small_derivative_probability (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (gaussianCoefficientMeasure (N + 1)).real {g | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (gaussianPolynomial N g) N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      gaussianAnnularDerivativeFailure (annularSmallDerivativeFailureConstant 1 K (K + 3)) N := by
  have hwidth : Tendsto (fun N : ℕ => ArcEnergy.arcScale * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul ArcEnergy.arcScale
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_annular_small_derivative_scalar_bounds (K' := K + 3) hK (by linarith) (by norm_num : (0 : ℝ) < 1)]
      with N hN hKN hKN' hdegree hwidthN hscalar
  let S := annularDerivativeScale K
  let L := (N : ℝ) ^ (1 / 64 : ℝ)
  let c := LocalZeroCount.localCountConstant (K + 3)
  let Q := (N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)
  let p := GaussianAnnularJetCount.pointProbabilityBound K (derivativeMeshValueThreshold N S L) (3 / L)
  let M : ℝ := Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L))
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hL : 1 ≤ L := Real.one_le_rpow hn.le (by norm_num)
  have hc : 0 < c := by unfold c LocalZeroCount.localCountConstant ArcEnergy.arcScale; positivity
  have hQ : 0 < Q := by unfold Q; positivity
  have hp : p ≤ 1 := (gaussian_pointProbability_le_annular_majorant N K _ _).trans hscalar.1
  have hmean : M * p ≤ Q / 2 := by
    apply (mul_le_mul_of_nonneg_left (gaussian_pointProbability_le_annular_majorant N K _ _)
      (show 0 ≤ M from Nat.cast_nonneg _)).trans
    convert hscalar.2.1 using 1
    dsimp [Q, c]
    ring
  have hB : GaussianAnnularSmallDerivative.annularLocalMultiplicityBound N (K + 2) ≤
      c * Real.log N := mul_le_mul_of_nonneg_right (gaussian_localCountConstant_le K) hlog.le
  have hBQ : (c * Real.log N) * Q = (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
    unfold Q
    field_simp
  have hsector : 40 * (c * Real.log N) * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2 := hscalar.2.2
  have hthreshold : GaussianAnnularSmallDerivative.annularLocalMultiplicityBound N (K + 2) * Q +
      40 * GaussianAnnularSmallDerivative.annularLocalMultiplicityBound N (K + 2) * Real.sqrt N ≤
      (N : ℝ) ^ (31 / 32 : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hB hQ.le
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 40))
      (Real.sqrt_nonneg N)
    rw [hBQ] at h₁
    linarith
  have hprob := GaussianAnnularSmallDerivative.annular_small_derivative_count N hN K (K + 2) L Q
    ((N : ℝ) ^ (31 / 32 : ℝ)) hK hKN hKN' le_rfl hL hwidthN.le hdegree hQ hmean hthreshold
  have hM : M ≤ annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN hK hS hL
  have htail : 4 * M ^ 2 * (GaussianAnnularJetCount.pairErrorConstant K + 5 * p) /
      (Real.sqrt N * Q ^ 2) ≤ annularSmallDerivativeFailureConstant 1 K (K + 3) *
        (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
    calc
      _ ≤ 4 * M ^ 2 * (annularJetPairConstant 1 K + 5 * p) / (Real.sqrt N * Q ^ 2) := by
        gcongr
        exact gaussian_pairError_le_annular_majorant K
      _ ≤ _ := annular_mesh_tail_rate_le hN hK (by norm_num : (0 : ℝ) < 1) hp (Nat.cast_nonneg _) hM
  unfold gaussianAnnularDerivativeFailure
  dsimp only [M, p] at htail
  linarith

end Erdos522

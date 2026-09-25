/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianAnnularJetCount
import Erdos522.Probability.CircularGaussianLocalZeroCount
import Erdos522.Probability.CircularGaussianSuprema
import Erdos522.Probability.CircularGaussianExceptionalSummability
import Erdos522.Probability.AnnularSmallDerivativeTransfer
import Erdos522.Probability.AnnularMeshThresholds

/-!
# Annular nondegeneracy for circular Gaussian polynomials

Exact Gaussian jet estimates, simultaneous local multiplicities and the
second-derivative envelope control all derivative-small annular roots. The
two real coordinates retain their separate exponential failure budgets.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The circular Gaussian mesh uses twice the real Gaussian curvature scale. -/
def circularGaussianAnnularDerivativeScale (K : ℝ) : ℝ := 2 * annularDerivativeScale K

/-- The finite coefficient in the circular Gaussian annular mesh failure. -/
def circularGaussianAnnularFailureConstant (K : ℝ) : ℝ :=
  16 * (LocalZeroCount.localCountConstant (K + 3)) ^ 2 *
    (annularJetPairConstant 1 K + 5) *
    (annularMeshSizeConstant K (circularGaussianAnnularDerivativeScale K)) ^ 2

/-- Circular Gaussian annular roots satisfy the derivative threshold and
count exponents with the complete summable failure envelope. -/
theorem eventually_circularGaussian_annular_small_derivative_probability
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
        {a | (N : ℝ) ^ (31 / 32 : ℝ) <
          (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) a) N K
            ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      circularGaussianAnnularDerivativeFailure (circularGaussianAnnularFailureConstant K) N := by
  let S := circularGaussianAnnularDerivativeScale K
  let c := LocalZeroCount.localCountConstant (K + 3)
  have hS : 1 ≤ S := by
    have h := one_le_annularDerivativeScale hK
    dsimp [S, circularGaussianAnnularDerivativeScale]
    linarith
  have hc : 0 < c := by
    unfold c LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  have hwidth : Tendsto (fun N : ℕ => ArcEnergy.arcScale * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul ArcEnergy.arcScale
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_annular_mesh_scalar_bounds hK hS hc (by norm_num : (0 : ℝ) < 1)]
      with N hN hKN hKN' hdegree hwidthN hscalar
  let L := (N : ℝ) ^ (1 / 64 : ℝ)
  let Q := (N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)
  let D := c * Real.log N
  let p := CircularGaussianAnnularJetCount.pointProbabilityBound K
    (derivativeMeshValueThreshold N S L) (3 / L)
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have hL : 1 ≤ L := Real.one_le_rpow hn.le (by norm_num)
  have hQ : 0 < Q := by unfold Q; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  have hmajor : p ≤ annularJetProbabilityBound N 1 K
      (derivativeMeshValueThreshold N S L) (3 / L) :=
    gaussian_pointProbability_le_annular_majorant N K _ _
  have hp : p ≤ 1 := hmajor.trans hscalar.1
  have hmean : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) * p ≤ Q / 2 := by
    apply (mul_le_mul_of_nonneg_left hmajor (Nat.cast_nonneg _)).trans
    convert hscalar.2.1 using 1
    dsimp [Q]
    ring
  have hDQ : D * Q = (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
    unfold D Q
    field_simp
  have hthreshold : D * Q + 40 * D * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) := by
    rw [hDQ]
    have hsector := hscalar.2.2
    linarith
  have hlocal : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {a | ∃ z : ℂ, |‖z‖ - 1| ≤ 1 / (N : ℝ) ∧ D <
        (zeroCountIn (Polynomial.ofFn (N + 1) a) (Metric.closedBall z (2 * (K + 2) / N)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 2 * Real.exp (-3 * (N + 1 : ℝ) / 32) := by
    apply (measureReal_mono ?_).trans
      (CircularGaussianLocalZeroCount.simultaneous_local_zero_count N hN hwidthN.le (by linarith : 0 ≤ K + 2))
    rintro a ⟨z, hz, hcount⟩
    refine ⟨z, hz, lt_of_le_of_lt ?_ hcount⟩
    exact mul_le_mul_of_nonneg_right (gaussian_localCountConstant_le K) hlog.le
  have hderivative := circularGaussian_second_derivative_supremum N hN hK hKN'
  have hmesh := CircularGaussianAnnularJetCount.annular_mesh_detection N hN K S L Q
    hK hKN hS hL hdegree hQ hmean
  have hM : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN hK hS hL
  have htail := annular_mesh_tail_rate_le_of_scale (c := c) hN hK (by norm_num : (0 : ℝ) < 1)
    hp (Nat.cast_nonneg _) hM
  have hmesh' : (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {a | Q ≤ (detectedAnnularMesh (Polynomial.ofFn (N + 1) a) N K S L).card} ≤
      circularGaussianAnnularFailureConstant K * (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
    apply hmesh.trans
    apply le_trans _ htail
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (gaussian_pairError_le_annular_majorant K) le_rfl
  have hcount := measure_annular_small_derivative_count_le
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)) (Polynomial.ofFn (N + 1))
    hN hK hS hL hD hKN' (by linarith : K + 1 ≤ 2 * (K + 2)) hthreshold hlocal
    (by simpa only [S, circularGaussianAnnularDerivativeScale, annularDerivativeScale,
      DerivativeSupremum.secondDerivativeEnvelope_eq, mul_assoc] using hderivative) hmesh'
  exact hcount.trans_eq (by unfold circularGaussianAnnularDerivativeFailure; ring)

end Erdos522

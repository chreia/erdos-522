/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GrowingAnnularDerivativeThresholds
import Erdos522.Probability.GrowingAnnularLogarithmicConcentration

/-!
# Small-derivative roots on a logarithmically growing annulus

The finite mesh theorem and its scalar thresholds give a summable exceptional
probability even when the annular width grows. The resulting almost-sure
count retains the original derivative and root-count powers.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- All mesh thresholds hold simultaneously at logarithmic width. -/
theorem eventually_growing_annular_derivative_scalar_bounds {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      let K := logarithmicAnnularWidth N
      let S := annularDerivativeScale K
      let L := (N : ℝ) ^ (1 / 64 : ℝ)
      annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S L) (3 / L) ≤ 1 ∧
      (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
        annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S L) (3 / L) ≤
        (N : ℝ) ^ (31 / 32 : ℝ) / (4 * LocalZeroCount.localCountConstant (K + 2) * Real.log N) ∧
      40 * annularLocalMultiplicityBound N (K + 2) * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_growing_annular_jet_probability hC).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_growing_annular_mean_ratio hC).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    tendsto_growing_annular_sector_ratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
      with N hN hp hmean hsector
  let K := logarithmicAnnularWidth N
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant (K + 2)
  have hK : 0 ≤ K := logarithmicAnnularWidth_nonneg N
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hc : 0 < c := by
    dsimp [c, LocalZeroCount.localCountConstant, ArcEnergy.arcScale]
    positivity
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have hpow : 0 < (N : ℝ) ^ (31 / 32 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 1 ≤ (N : ℝ) ^ (1 / 64 : ℝ) := Real.one_le_rpow hn.le (by norm_num)
  have hprob : 0 ≤ annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
        (3 / (N : ℝ) ^ (1 / 64 : ℝ)) := by
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos C K hC
    positivity
  refine ⟨hp.le, ?_, ?_⟩
  · have hcard := annular_mesh_cardinality_le (K := K) hN hK hS hL
    have hc' : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N S ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) ≤
        annularMeshSizeConstant K S * N * ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N := by
      simpa only [annularMeshSizeConstant, mul_assoc] using hcard
    apply (mul_le_mul_of_nonneg_right hc' hprob).trans
    apply (le_div_iff₀ (show 0 < 4 * c * Real.log N by positivity)).mpr
    simpa only [one_mul] using ((div_lt_one hpow).mp hmean).le
  · have hsector' := (div_lt_one hpow).mp hsector
    dsimp [annularLocalMultiplicityBound]
    linarith

/-- Direct use of the finite mesh theorem gives the complete growing-width failure bound. -/
theorem eventually_growing_annular_derivative_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (LogMoments.signMeasure N).real {ω | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N (logarithmicAnnularWidth N)
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
        annularSmallDerivativeFailureConstant C (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2) *
          (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_annular_small_derivative_failure_constants
  refine ⟨C₂, hC₂, ?_⟩
  have hwidth : Tendsto (fun N : ℕ => ArcEnergy.arcScale * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul ArcEnergy.arcScale
  have hKratio := tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 1)
    (by norm_num) (by norm_num) 1 0
  simp only [pow_one, pow_zero, zero_mul, Real.exp_zero, mul_one, Real.rpow_one] at hKratio
  filter_upwards [eventually_logarithmicAnnularWidth_degree_conditions,
    eventually_growing_annular_derivative_scalar_bounds hC₁,
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hKratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN hscalar hwidthN hratio
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact hprob N hN.1 (logarithmicAnnularWidth N) (logarithmicAnnularWidth N + 2)
    (logarithmicAnnularWidth_nonneg N) hN.2.2.1 ((div_lt_one hn).mp hratio).le
    le_rfl hwidthN.le hN.2.2.2 hscalar.1 hscalar.2.1 hscalar.2.2

/-- On every sufficiently sparse rounded power schedule, only `N^(31/32)`
roots in the growing annulus have derivative below `N^(3/2)/N^(1/64)`, almost surely. -/
theorem ae_eventually_growing_annular_derivative_count {q : ℝ} (hq : 500 / 181 < q) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      let N := realPowerDegree q j
      (annularSmallDerivativeZeroCount (rademacherPolynomial N (rademacherPrefix N ω)) N
        (logarithmicAnnularWidth N) ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (31 / 32 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := eventually_growing_annular_derivative_probability
  let E (N : ℕ) : Set (LogMoments.SignVector N) := {v | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (rademacherPolynomial N v) N (logarithmicAnnularWidth N)
      ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}
  have hq0 : 0 < q := by linarith
  have hsum₁ : Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 3) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_ofNat, one_div] using
      summable_realPowerDegree_rpow hq0 (a := -(3 : ℝ)) (by linarith)
  have hsum₂ : Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 10) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_ofNat, one_div] using
      summable_realPowerDegree_rpow hq0 (a := -(10 : ℝ)) (by linarith)
  have hsum₃ := summable_logarithmicAnnularWidth_badRootFailure hq hC
  have hs : Summable (fun j : ℕ => (LogMoments.signMeasure (realPowerDegree q j)).real (E (realPowerDegree q j))) := by
    apply ((hsum₁.add hsum₂).add hsum₃).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_realPowerDegree hq0).eventually hbound] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  filter_upwards [ae_eventually_rademacherPrefix_notMem (realPowerDegree q) E hs] with ω hω
  filter_upwards [hω] with j hj
  exact le_of_not_gt hj

end Erdos522

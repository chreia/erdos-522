/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeLimits

/-!
# Annular mesh thresholds with an arbitrary derivative scale

For each fixed positive local-count coefficient and derivative envelope,
the mesh mean and sector count are eventually smaller than the count budget.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- Every finite scalar condition holds for a fixed derivative mesh scale and
local multiplicity coefficient. -/
theorem eventually_annular_mesh_scalar_bounds {K S c C : ℝ}
    (hK : 0 ≤ K) (hS : 1 ≤ S) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      annularJetProbabilityBound N C K
        (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤ 1 ∧
      (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N S ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) *
        annularJetProbabilityBound N C K
          (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
            (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤
        (N : ℝ) ^ (31 / 32 : ℝ) / (4 * c * Real.log N) ∧
      40 * (c * Real.log N) * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_annularJetProbabilityBound hSp C K).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_mean_ratio hSp C K c).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_sector_ratio c).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
      with N hN hp hmean hsector
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
    linarith


/-- The specialized mesh tail has the stated polynomial failure rate. -/
theorem annular_mesh_tail_rate_le_of_scale {N : ℕ} (hN : 2 ≤ N) {K S c C p M : ℝ}
    (_hK : 0 ≤ K) (hC : 0 < C) (hp : p ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ annularMeshSizeConstant K S * N *
      ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N) :
    4 * M ^ 2 * (annularJetPairConstant C K + 5 * p) /
      (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) ≤
      16 * c ^ 2 * (annularJetPairConstant C K + 5) *
        (annularMeshSizeConstant K S) ^ 2 *
        (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : 0 ≤ annularJetPairConstant C K + 5 := by
    have hpos := annularJetPairConstant_pos C K hC
    linarith
  have hMsq := pow_le_pow_left₀ hM0 hM 2
  calc
    _ ≤ 4 * M ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : annularJetPairConstant C K + 5 * p ≤
          annularJetPairConstant C K + 5) (by positivity)) (by positivity)
    _ ≤ 4 * (annularMeshSizeConstant K S * N *
        ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N) ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq (by norm_num)) hV) (by positivity)
    _ = _ := annular_mesh_rate_identity hNr


end Erdos522

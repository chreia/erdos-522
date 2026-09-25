/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausAnnularSmallDerivative
import Erdos522.Probability.AnnularSmallDerivativeLimits

/-!
# Quantitative annular nondegeneracy for Steinhaus polynomials

The finite mesh estimate at derivative scale `N^(1/64)` gives a root-count
threshold `N^(31/32)`. Its three failure terms are summable along eighth
powers. Every fixed-width scalar condition follows from the same explicit
annular probability envelopes.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The actual annular small-derivative count has failure `N⁻³ + N⁻¹⁰ + C N⁻³/⁸(log N)⁴`. -/
theorem exists_steinhaus_annular_small_derivative_failure_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K K' : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : K + 1 ≤ (N : ℝ)) (_ : K + 2 ≤ K')
      (_ : ArcEnergy.arcScale * Real.log N / N ≤ 1)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : annularJetProbabilityBound N C₁ K
        (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤ 1)
      (_ : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) *
        annularJetProbabilityBound N C₁ K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
            (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤
        (N : ℝ) ^ (31 / 32 : ℝ) / (4 * LocalZeroCount.localCountConstant K' * Real.log N))
      (_ : 40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2),
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
        annularSmallDerivativeFailureConstant C₂ K K' *
          (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_steinhaus_annular_small_derivative_constants
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K K' hK hKN hKN' hKK' hwidth hdegree hp hmean hsector
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hNr
  have hK' : 0 ≤ K' := by linarith
  have hc : 0 < LocalZeroCount.localCountConstant K' := by
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  let L := (N : ℝ) ^ (1 / 64 : ℝ)
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant K'
  let Q := (N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)
  have hL : 1 ≤ L := Real.one_le_rpow hNr.le (by norm_num)
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hQ : 0 < Q := by dsimp [Q, c]; positivity
  have hmean' : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2 := by
    convert hmean using 1
    dsimp [Q, c]
    ring
  have hBQ : annularLocalMultiplicityBound N K' * Q = (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
    dsimp [annularLocalMultiplicityBound, Q, c]
    field_simp
  have hthreshold : annularLocalMultiplicityBound N K' * Q +
      40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) := by
    rw [hBQ]
    linarith
  have h := hprob N hN K K' L Q ((N : ℝ) ^ (31 / 32 : ℝ)) hK hKN hKN' hKK' hL
    hwidth hdegree hQ hmean' hthreshold
  apply h.trans
  apply add_le_add_right
  have hM : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN hK hS hL
  exact annular_mesh_tail_rate_le hN hK hC₂ hp (Nat.cast_nonneg _) hM


/-- Fixed annular widths admit an unconditional eventual quantitative small-derivative estimate. -/
theorem eventually_steinhaus_annular_small_derivative_probability (K K' : ℝ)
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 + C *
        (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_steinhaus_annular_small_derivative_failure_constants
  let C := annularSmallDerivativeFailureConstant C₂ K K'
  have hC : 0 < C := by
    have hK' : 0 ≤ K' := by linarith
    have hV := annularJetPairConstant_pos C₂ K hC₂
    dsimp [C, annularSmallDerivativeFailureConstant, annularMeshSizeConstant,
      LocalZeroCount.localCountConstant, ArcEnergy.arcScale, annularDerivativeScale]
    positivity
  refine ⟨C, hC, ?_⟩
  have hwidth : Tendsto (fun N : ℕ => ArcEnergy.arcScale * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul ArcEnergy.arcScale
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_annular_small_derivative_scalar_bounds hK hKK' hC₁]
      with N hN hKN hKN' hdegree hwidthN hscalar
  exact hprob N hN K K' hK hKN hKN' hKK' hwidthN.le hdegree hscalar.1 hscalar.2.1 hscalar.2.2

end Erdos522

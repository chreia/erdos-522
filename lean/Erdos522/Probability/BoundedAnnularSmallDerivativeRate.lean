/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedAnnularSmallDerivative
import Erdos522.Probability.AnnularMeshThresholds
import Erdos522.Probability.AnnularSmallDerivativeSummability
import Erdos522.Probability.CoefficientSequence

/-!
# Summable annular nondegeneracy for bounded symmetric laws

The fixed derivative scale and local multiplicity coefficient affect the
finite constants but preserve the `N⁻³/⁸ (log N)⁴` mesh failure rate. The
result applies to one shared coefficient sequence, including laws with a
positive atom at zero.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The failure constant with the coefficient-dependent mesh and local count. -/
def boundedAnnularSmallDerivativeFailureConstant (C B K K' : ℝ) : ℝ :=
  16 * (BoundedLocalZeroCount.localCountConstant B K') ^ 2 *
    (annularJetPairConstant C K + 5) *
    (annularMeshSizeConstant K (boundedAnnularDerivativeScale B K)) ^ 2

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {B : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hmean : (∫ z, z ∂μ) = 0) (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hmean hsecond

/-- Fixed annuli have an explicit eventually valid small-derivative failure envelope. -/
theorem eventually_bounded_annular_small_derivative_probability (K K' : ℝ)
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real {a | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) a) N K
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
        C * (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ :=
    exists_bounded_annular_small_derivative_constants μ hB hbound hmean hsecond
  let S := boundedAnnularDerivativeScale B K
  let c := BoundedLocalZeroCount.localCountConstant B K'
  have hS : 1 ≤ S := one_le_boundedAnnularDerivativeScale hB hK
  have hc : 0 < c := by
    have hK' : 0 ≤ K' := by linarith
    have hl := Real.log_nonneg hB
    unfold c BoundedLocalZeroCount.localCountConstant BoundedLocalZeroCount.arcScale
    positivity
  let C := boundedAnnularSmallDerivativeFailureConstant C₂ B K K'
  have hC : 0 < C := by
    have hV := annularJetPairConstant_pos C₂ K hC₂
    change 0 < 16 * c ^ 2 * (annularJetPairConstant C₂ K + 5) *
      (annularMeshSizeConstant K S) ^ 2
    unfold annularMeshSizeConstant
    positivity
  refine ⟨C, hC, ?_⟩
  have hwidth : Tendsto (fun N : ℕ =>
      BoundedLocalZeroCount.arcScale B * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul
        (BoundedLocalZeroCount.arcScale B)
  have hamp : Tendsto (fun N : ℕ => 12 * B ^ 4 * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul (12 * B ^ 4)
  filter_upwards [eventually_ge_atTop 4,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hamp.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_annular_mesh_scalar_bounds hK hS hc hC₁]
      with N hN hKN hKN' hdegree hwidthN hampN hscalar
  have hN2 : 2 ≤ N := by omega
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  let L := (N : ℝ) ^ (1 / 64 : ℝ)
  let Q := (N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)
  have hL : 1 ≤ L := Real.one_le_rpow hn.le (by norm_num)
  have hQ : 0 < Q := by unfold Q; positivity
  have hamplitude : 12 * B ^ 4 * Real.log N ≤ N + 1 := by
    have h := (div_lt_one (zero_lt_one.trans hn)).mp hampN
    linarith
  have hmeshmean : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2 := by
    convert hscalar.2.1 using 1
    dsimp [Q]
    ring
  have hDQ : boundedAnnularMultiplicityBound N B K' * Q =
      (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
    change (c * Real.log N) * Q = _
    dsimp [Q]
    field_simp
  have hthreshold : boundedAnnularMultiplicityBound N B K' * Q +
      40 * boundedAnnularMultiplicityBound N B K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) := by
    rw [hDQ]
    have hsector := hscalar.2.2
    change 40 * boundedAnnularMultiplicityBound N B K' * Real.sqrt N ≤ _ at hsector
    linarith
  have h := hprob N hN K K' L Q ((N : ℝ) ^ (31 / 32 : ℝ)) hK hKN hKN' hKK' hL
    hwidthN.le hamplitude hdegree hQ hmeshmean hthreshold
  apply h.trans
  apply add_le_add_right
  have hM : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN2 hK hS hL
  exact annular_mesh_tail_rate_le_of_scale hN2 hK hC₂ hscalar.1 (Nat.cast_nonneg _) hM

/-- Borel–Cantelli yields the sparse quantitative annular root count for one
infinite bounded symmetric coefficient sequence. -/
theorem ae_eventually_bounded_annular_small_derivative_count (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure μ, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (Polynomial.ofFn (j ^ 8 + 1) (coefficientPrefix (j ^ 8) ω)) (j ^ 8) K
          (((j ^ 8 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ ((j ^ 8 : ℕ) : ℝ) ^ (31 / 32 : ℝ) := by
  let E (N : ℕ) : Set (Fin (N + 1) → ℂ) := {a | (N : ℝ) ^ (31 / 32 : ℝ) <
    (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) a) N K ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)}
  obtain ⟨C, _, hC⟩ := eventually_bounded_annular_small_derivative_probability
    μ hB hbound hmean hsecond K (K + 2) hK le_rfl
  have hs : Summable (fun j : ℕ =>
      (Measure.pi (fun _ : Fin (j ^ 8 + 1) => μ)).real (E (j ^ 8))) := by
    apply (summable_annular_failure_envelope C).of_norm_bounded_eventually_nat
    filter_upwards [(tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)).eventually hC] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hj
  filter_upwards [ae_eventually_indexed_coefficientPrefix_notMem μ
    (fun j => j ^ 8) (fun j => E (j ^ 8)) hs] with ω hω
  exact hω.mono fun _ hj => le_of_not_gt hj

end Erdos522

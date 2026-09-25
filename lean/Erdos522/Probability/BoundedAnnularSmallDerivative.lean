/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.BoundedAnnularJetCount
import Erdos522.Probability.AnnularSmallDerivativeRate
import Erdos522.Probability.BoundedLocalZeroCountRate
import Erdos522.Probability.BoundedPolynomialSuprema

/-!
# Annular nondegeneracy for bounded symmetric coefficients

Local zero counts and joint small-ball probabilities control the multiplicity
of derivative-small annular zeros. The coefficient modulus bound appears in
the derivative mesh and in the local-count constant, with both finite
thresholds kept explicit.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Erdos522

/-- The second-derivative mesh scale for a coefficient bound `B`. -/
def boundedAnnularDerivativeScale (B K : ℝ) : ℝ := B * annularDerivativeScale K

/-- The local multiplicity budget for bounded symmetric coefficients. -/
def boundedAnnularMultiplicityBound (N : ℕ) (B K : ℝ) : ℝ :=
  BoundedLocalZeroCount.localCountConstant B K * Real.log N

theorem one_le_boundedAnnularDerivativeScale {B K : ℝ} (hB : 1 ≤ B) (hK : 0 ≤ K) :
    1 ≤ boundedAnnularDerivativeScale B K :=
  one_le_mul_of_one_le_of_one_le hB (one_le_annularDerivativeScale hK)

variable (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant] {B : ℝ}
    (hB : 1 ≤ B) (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B)
    (hmean : (∫ z, z ∂μ) = 0) (hsecond : (∫ z, ‖z‖ ^ 2 ∂μ) = 1)

include hB hbound hmean hsecond

/-- Bounded symmetric coefficient control of all annular small-derivative zeros, with three explicit failure terms. -/
theorem exists_bounded_annular_small_derivative_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 4 ≤ N) (K K' L Q T : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : K + 1 ≤ (N : ℝ)) (_ : K + 2 ≤ K') (_ : 1 ≤ L)
      (_ : BoundedLocalZeroCount.arcScale B * Real.log N / N ≤ 1)
      (_ : 12 * B ^ 4 * Real.log N ≤ N + 1)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (_ : 0 < Q)
      (_ : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (boundedAnnularDerivativeScale B K) L)) : ℝ) *
        annularJetProbabilityBound N C₁ K
          (derivativeMeshValueThreshold N (boundedAnnularDerivativeScale B K) L) (3 / L) ≤ Q / 2)
      (_ : boundedAnnularMultiplicityBound N B K' * Q +
        40 * boundedAnnularMultiplicityBound N B K' * Real.sqrt N ≤ T),
      (Measure.pi (fun _ : Fin (N + 1) => μ)).real {ω | T <
        (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K L : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
      4 * (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (boundedAnnularDerivativeScale B K) L)) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K +
          5 * annularJetProbabilityBound N C₁ K
            (derivativeMeshValueThreshold N (boundedAnnularDerivativeScale B K) L) (3 / L)) /
        (Real.sqrt N * Q ^ 2) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  obtain ⟨C₁, C₂, hC₁, hC₂, hmesh⟩ := BoundedAnnularJetCount.exists_annular_mesh_detection_constants μ hB0 hbound hmean hsecond
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K K' L Q T hK hKN hKN' hKK' hL hwidth hamplitude hdegree hQ hmeshmean hthreshold
  let S := boundedAnnularDerivativeScale B K
  let D := boundedAnnularMultiplicityBound N B K'
  have hN2 : 2 ≤ N := by omega
  have hS : 1 ≤ S := one_le_boundedAnnularDerivativeScale hB hK
  have hK' : 0 ≤ K' := by linarith
  have hD : 0 ≤ D := by
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hlogB := Real.log_nonneg hB
    unfold D boundedAnnularMultiplicityBound BoundedLocalZeroCount.localCountConstant
      BoundedLocalZeroCount.arcScale
    positivity
  let E₁ : Set (Fin (N + 1) → ℂ) := {ω | ∃ c : ℂ,
    |‖c‖ - 1| ≤ 1 / (N : ℝ) ∧ D <
      (zeroCountIn (Polynomial.ofFn (N + 1) ω) (Metric.closedBall c (2 * K' / N)) : ℝ)}
  let E₂ : Set (Fin (N + 1) → ℂ) := {ω | ∃ w : ℂ,
    ‖w‖ ≤ 1 + (K + 1) / N ∧ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
      ‖(Polynomial.ofFn (N + 1) ω).derivative.derivative.eval w‖}
  let E₃ : Set (Fin (N + 1) → ℂ) := {ω | Q ≤
    (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card}
  have hprob₁ : (Measure.pi (fun _ : Fin (N + 1) => μ)).real E₁ ≤ 1 / (N : ℝ) ^ 3 :=
    BoundedLocalZeroCount.simultaneous_local_zero_count N hN (fun _ => μ) hB hK'
      (fun _ => hbound) (fun _ => hsecond) hwidth hamplitude
  have hprob₂ : (Measure.pi (fun _ : Fin (N + 1) => μ)).real E₂ ≤ 1 / (N : ℝ) ^ 10 :=
    by
      have h := BoundedPolynomialSuprema.second_derivative_supremum N hN2
        (fun _ => μ) hB0 hK hKN' (fun _ => hbound) (fun _ => hmean)
      simpa only [E₂, S, boundedAnnularDerivativeScale, annularDerivativeScale,
        DerivativeSupremum.secondDerivativeEnvelope_eq, mul_assoc] using h
  have hprob₃ := hmesh N hN2 K S L Q hK hKN hS hL hdegree hQ hmeshmean
  have hsub : {ω | T < (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K L : ℝ)} ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hlocal (c : ℂ) (hc : ‖c‖ = 1) :
        (zeroCountIn (Polynomial.ofFn (N + 1) ω) (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ D := by
      apply le_of_not_gt
      intro hbad
      apply h₁
      exact ⟨c, by rw [hc, sub_self, abs_zero]; positivity, hbad⟩
    have hbound (w : ℂ) (hw : ‖w‖ ≤ 1 + (K + 1) / N) :
        ‖(Polynomial.ofFn (N + 1) ω).derivative.derivative.eval w‖ ≤
          S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) := by
      apply le_of_not_gt
      intro hbad
      exact h₂ ⟨w, hw, hbad⟩
    have hcount := full_annular_small_derivative_count_le (Polynomial.ofFn (N + 1) ω) hN2 hK hS hL hD
      hKN' (by linarith : K + 1 ≤ 2 * K') hbound hlocal
    have hdet : ((detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card : ℝ) ≤ Q :=
      (lt_of_not_ge h₃).le
    have hupper : (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K L : ℝ) ≤ T := by
      apply hcount.trans
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hdet hD) _).trans
        (by simpa only [mul_comm Q D] using hthreshold)
    exact (not_lt_of_ge hupper hω).elim
  calc
    _ ≤ (Measure.pi (fun _ : Fin (N + 1) => μ)).real (E₁ ∪ E₂ ∪ E₃) := measureReal_mono hsub
    _ ≤ (Measure.pi (fun _ : Fin (N + 1) => μ)).real E₁ + (Measure.pi (fun _ : Fin (N + 1) => μ)).real E₂ +
        (Measure.pi (fun _ : Fin (N + 1) => μ)).real E₃ :=
      (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hprob₁ hprob₂) hprob₃

end Erdos522

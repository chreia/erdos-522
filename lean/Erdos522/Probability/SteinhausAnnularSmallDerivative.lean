/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausAnnularJetCount
import Erdos522.Probability.AnnularSmallDerivative
import Erdos522.Probability.ComplexLocalZeroCount
import Erdos522.Probability.BoundedPolynomialSuprema

/-!
# Annular small-derivative zeros of Steinhaus polynomials

A derivative supremum detects roots on the annular mesh. Local multiplicity
bounds convert the mesh count and the omitted angular sectors into a count
of zeros, including repeated roots.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Erdos522

/-- Steinhaus-law control of all annular small-derivative zeros, with three explicit failure terms. -/
theorem exists_steinhaus_annular_small_derivative_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K K' L Q T : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : K + 1 ≤ (N : ℝ)) (_ : K + 2 ≤ K') (_ : 1 ≤ L)
      (_ : ArcEnergy.arcScale * Real.log N / N ≤ 1)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) (_ : 0 < Q)
      (_ : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) L)) : ℝ) *
        annularJetProbabilityBound N C₁ K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) L) (3 / L) ≤ Q / 2)
      (_ : annularLocalMultiplicityBound N K' * Q +
        40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ T),
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real {ω | T <
        (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K L : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
      4 * (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) L)) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K +
          5 * annularJetProbabilityBound N C₁ K
            (derivativeMeshValueThreshold N (annularDerivativeScale K) L) (3 / L)) /
        (Real.sqrt N * Q ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hmesh⟩ := SteinhausAnnularJetCount.exists_annular_mesh_detection_constants
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K K' L Q T hK hKN hKN' hKK' hL hwidth hdegree hQ hmean hthreshold
  let S := annularDerivativeScale K
  let B := annularLocalMultiplicityBound N K'
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hK' : 0 ≤ K' := by linarith
  have hB : 0 ≤ B := annularLocalMultiplicityBound_nonneg hN hK'
  let E₁ : Set (Fin (N + 1) → ℂ) := {ω | ∃ c : ℂ,
    |‖c‖ - 1| ≤ 1 / (N : ℝ) ∧ B <
      (zeroCountIn (Polynomial.ofFn (N + 1) ω) (Metric.closedBall c (2 * K' / N)) : ℝ)}
  let E₂ : Set (Fin (N + 1) → ℂ) := {ω | ∃ w : ℂ,
    ‖w‖ ≤ 1 + (K + 1) / N ∧ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
      ‖(Polynomial.ofFn (N + 1) ω).derivative.derivative.eval w‖}
  let E₃ : Set (Fin (N + 1) → ℂ) := {ω | Q ≤
    (detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card}
  have hprob₁ : (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real E₁ ≤ 1 / (N : ℝ) ^ 3 :=
    ComplexLocalZeroCount.steinhaus_local_zero_count N hN hwidth hK'
  have hprob₂ : (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real E₂ ≤ 1 / (N : ℝ) ^ 10 :=
    by
      have h := BoundedPolynomialSuprema.second_derivative_supremum N hN
        (fun _ => steinhausMeasure) (B := 1) (by norm_num) hK hKN'
        (fun _ => ae_norm_steinhaus_eq_one.mono fun _ hz => hz.le)
        (fun _ => integral_steinhaus)
      simpa only [E₂, S, annularDerivativeScale, DerivativeSupremum.secondDerivativeEnvelope_eq,
        one_mul] using h
  have hprob₃ := hmesh N hN K S L Q hK hKN hS hL hdegree hQ hmean
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
        (zeroCountIn (Polynomial.ofFn (N + 1) ω) (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B := by
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
    have hcount := full_annular_small_derivative_count_le (Polynomial.ofFn (N + 1) ω) hN hK hS hL hB
      hKN' (by linarith : K + 1 ≤ 2 * K') hbound hlocal
    have hdet : ((detectedAnnularMesh (Polynomial.ofFn (N + 1) ω) N K S L).card : ℝ) ≤ Q :=
      (lt_of_not_ge h₃).le
    have hupper : (annularSmallDerivativeZeroCount (Polynomial.ofFn (N + 1) ω) N K L : ℝ) ≤ T := by
      apply hcount.trans
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hdet hB) _).trans
        (by simpa only [mul_comm Q B] using hthreshold)
    exact (not_lt_of_ge hupper hω).elim
  calc
    _ ≤ (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E₁ ∪ E₂ ∪ E₃) := measureReal_mono hsub
    _ ≤ (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real E₁ + (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real E₂ +
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real E₃ :=
      (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hprob₁ hprob₂) hprob₃

end Erdos522

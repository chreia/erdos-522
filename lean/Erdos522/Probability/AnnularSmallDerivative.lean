/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularJetCount
import Erdos522.Probability.DerivativeSupremum
import Erdos522.Stability.SectorRootCount

/-!
# Annular small-derivative zeros of Rademacher polynomials

A uniform second-derivative bound detects every small-derivative zero on the
annular mesh. The simultaneous local zero count bounds the multiplicity in
each cell and the omitted real sectors. Combining these deterministic facts
with the finite jet-count concentration gives a quantitative probability
bound for the full annular zero count.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Erdos522

/-- The coefficient in the uniform second-derivative envelope. -/
def annularDerivativeScale (K : ℝ) : ℝ := 100 * Real.exp (K + 4)

/-- The second-derivative scale is at least one on every nonnegative-width annulus. -/
theorem one_le_annularDerivativeScale {K : ℝ} (hK : 0 ≤ K) : 1 ≤ annularDerivativeScale K := by
  have he : 1 ≤ Real.exp (K + 4) := Real.one_le_exp_iff.mpr (by linarith)
  dsimp [annularDerivativeScale]
  linarith

/-- Annular zeros at or below the derivative threshold, counted with multiplicity. -/
def annularSmallDerivativeZeroCount (P : Polynomial ℂ) (N : ℕ) (K L : ℝ) : ℕ :=
  zeroCountIn P {α | |‖α‖ - 1| ≤ K / N ∧
    ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L}

/-- The local multiplicity bound used for every mesh cell and real-sector disk. -/
def annularLocalMultiplicityBound (N : ℕ) (K' : ℝ) : ℝ :=
  LocalZeroCount.localCountConstant K' * Real.log N

/-- The local multiplicity bound is nonnegative in the range of the local-count theorem. -/
theorem annularLocalMultiplicityBound_nonneg {N : ℕ} (hN : 2 ≤ N) {K' : ℝ} (hK' : 0 ≤ K') :
    0 ≤ annularLocalMultiplicityBound N K' := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  unfold annularLocalMultiplicityBound LocalZeroCount.localCountConstant ArcEnergy.arcScale
  positivity

/-- Actual sign-law control of all annular small-derivative zeros, with three explicit failure terms. -/
theorem exists_annular_small_derivative_constants :
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
      (LogMoments.signMeasure N).real {ω | T <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K L : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
      4 * (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) L)) : ℝ) ^ 2 *
        (annularJetPairConstant C₂ K +
          5 * annularJetProbabilityBound N C₁ K
            (derivativeMeshValueThreshold N (annularDerivativeScale K) L) (3 / L)) /
        (Real.sqrt N * Q ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hmesh⟩ := exists_annular_mesh_detection_constants
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K K' L Q T hK hKN hKN' hKK' hL hwidth hdegree hQ hmean hthreshold
  let S := annularDerivativeScale K
  let B := annularLocalMultiplicityBound N K'
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hK' : 0 ≤ K' := by linarith
  have hB : 0 ≤ B := annularLocalMultiplicityBound_nonneg hN hK'
  let E₁ : Set (LogMoments.SignVector N) := {ω | ∃ c : ℂ,
    |‖c‖ - 1| ≤ 1 / (N : ℝ) ∧ B <
      (zeroCountIn (rademacherPolynomial N ω) (Metric.closedBall c (2 * K' / N)) : ℝ)}
  let E₂ : Set (LogMoments.SignVector N) := {ω | ∃ w : ℂ,
    ‖w‖ ≤ 1 + (K + 1) / N ∧ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
      ‖(rademacherPolynomial N ω).derivative.derivative.eval w‖}
  let E₃ : Set (LogMoments.SignVector N) := {ω | Q ≤
    (detectedAnnularMesh (rademacherPolynomial N ω) N K S L).card}
  have hprob₁ : (LogMoments.signMeasure N).real E₁ ≤ 1 / (N : ℝ) ^ 3 :=
    LocalZeroCount.simultaneous_local_zero_count N hN hwidth hK'
  have hprob₂ : (LogMoments.signMeasure N).real E₂ ≤ 1 / (N : ℝ) ^ 10 :=
    DerivativeSupremum.annular_derivative_supremum N hN hK hKN'
  have hprob₃ := hmesh N hN K S L Q hK hKN hS hL hdegree hQ hmean
  have hsub : {ω | T < (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K L : ℝ)} ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hlocal (c : ℂ) (hc : ‖c‖ = 1) :
        (zeroCountIn (rademacherPolynomial N ω) (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B := by
      apply le_of_not_gt
      intro hbad
      apply h₁
      exact ⟨c, by rw [hc, sub_self, abs_zero]; positivity, hbad⟩
    have hbound (w : ℂ) (hw : ‖w‖ ≤ 1 + (K + 1) / N) :
        ‖(rademacherPolynomial N ω).derivative.derivative.eval w‖ ≤
          S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) := by
      apply le_of_not_gt
      intro hbad
      exact h₂ ⟨w, hw, hbad⟩
    have hcount := full_annular_small_derivative_count_le (rademacherPolynomial N ω) hN hK hS hL hB
      hKN' (by linarith : K + 1 ≤ 2 * K') hbound hlocal
    have hdet : ((detectedAnnularMesh (rademacherPolynomial N ω) N K S L).card : ℝ) ≤ Q :=
      (lt_of_not_ge h₃).le
    have hupper : (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K L : ℝ) ≤ T := by
      apply hcount.trans
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hdet hB) _).trans
        (by simpa only [mul_comm Q B] using hthreshold)
    exact (not_lt_of_ge hupper hω).elim
  calc
    _ ≤ (LogMoments.signMeasure N).real (E₁ ∪ E₂ ∪ E₃) := measureReal_mono hsub
    _ ≤ (LogMoments.signMeasure N).real E₁ + (LogMoments.signMeasure N).real E₂ +
        (LogMoments.signMeasure N).real E₃ :=
      (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hprob₁ hprob₂) hprob₃

end Erdos522

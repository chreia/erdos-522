/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivative

/-!
# Transferring annular mesh estimates to root counts

Three exceptional probabilities suffice: local multiplicity, the second
 derivative supremum and the detected mesh count. Their union controls all
annular derivative-small roots with multiplicity for any polynomial law.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- Local multiplicity, curvature and mesh-detection bounds imply an annular
small-derivative count bound under an arbitrary polynomial distribution. -/
theorem measure_annular_small_derivative_count_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N) {K K' S L D Q T p₁ p₂ p₃ : ℝ}
    (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hKN : K + 1 ≤ (N : ℝ)) (hKK' : K + 1 ≤ 2 * K')
    (hthreshold : D * Q + 40 * D * Real.sqrt N ≤ T)
    (hlocal : μ.real {ω | ∃ c : ℂ, |‖c‖ - 1| ≤ 1 / (N : ℝ) ∧
      D < (zeroCountIn (P ω) (Metric.closedBall c (2 * K' / N)) : ℝ)} ≤ p₁)
    (hderivative : μ.real {ω | ∃ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N ∧
      S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
        ‖(P ω).derivative.derivative.eval z‖} ≤ p₂)
    (hmesh : μ.real {ω | Q ≤ (detectedAnnularMesh (P ω) N K S L).card} ≤ p₃) :
    μ.real {ω | T < (annularSmallDerivativeZeroCount (P ω) N K L : ℝ)} ≤ p₁ + p₂ + p₃ := by
  let E₁ : Set Ω := {ω | ∃ c : ℂ, |‖c‖ - 1| ≤ 1 / (N : ℝ) ∧
    D < (zeroCountIn (P ω) (Metric.closedBall c (2 * K' / N)) : ℝ)}
  let E₂ : Set Ω := {ω | ∃ z : ℂ, ‖z‖ ≤ 1 + (K + 1) / N ∧
    S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) <
      ‖(P ω).derivative.derivative.eval z‖}
  let E₃ : Set Ω := {ω | Q ≤ (detectedAnnularMesh (P ω) N K S L).card}
  have hsub : {ω | T < (annularSmallDerivativeZeroCount (P ω) N K L : ℝ)} ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_cases h₁ : ω ∈ E₁
    · exact Or.inl (Or.inl h₁)
    by_cases h₂ : ω ∈ E₂
    · exact Or.inl (Or.inr h₂)
    by_cases h₃ : ω ∈ E₃
    · exact Or.inr h₃
    have hlocal' (c : ℂ) (hc : ‖c‖ = 1) :
        (zeroCountIn (P ω) (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ D := by
      apply le_of_not_gt
      intro hbad
      exact h₁ ⟨c, by rw [hc, sub_self, abs_zero]; positivity, hbad⟩
    have hderivative' (z : ℂ) (hz : ‖z‖ ≤ 1 + (K + 1) / N) :
        ‖(P ω).derivative.derivative.eval z‖ ≤
          S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N) :=
      le_of_not_gt (fun hbad => h₂ ⟨z, hz, hbad⟩)
    have hcount := full_annular_small_derivative_count_le (P ω) hN hK hS hL hD
      hKN hKK' hderivative' hlocal'
    have hdet : ((detectedAnnularMesh (P ω) N K S L).card : ℝ) ≤ Q := (lt_of_not_ge h₃).le
    have hupper : (annularSmallDerivativeZeroCount (P ω) N K L : ℝ) ≤ T := by
      apply hcount.trans
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hdet hD) _).trans
        (by simpa only [mul_comm Q D] using hthreshold)
    exact (not_lt_of_ge hupper hω).elim
  calc
    _ ≤ μ.real (E₁ ∪ E₂ ∪ E₃) := measureReal_mono hsub
    _ ≤ μ.real E₁ + μ.real E₂ + μ.real E₃ :=
      (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hlocal hderivative) hmesh

end Erdos522

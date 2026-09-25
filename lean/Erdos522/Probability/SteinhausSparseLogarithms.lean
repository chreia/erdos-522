/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausConcentrationRate
import Erdos522.Probability.CoefficientSequence
import Erdos522.Probability.SparseLogarithmicConcentration

/-!
# Sparse Steinhaus logarithmic circle averages

The finite-family logarithmic concentration bounds are summable along every
degree sequence `j^s` with `3s > 8`. Borel–Cantelli is applied to consistent
prefixes of one infinite circular coefficient sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace Erdos522

/-- A finite family of radial logarithmic deviations. -/
def steinhausRadialLogarithmicFailure {ι : Type*} (N : ℕ) (r : ι → ℝ) : Set (Fin (N + 1) → ℂ) :=
  {ω | ∃ i, logarithmicTolerance N <
    |logCircleAverage (Polynomial.ofFn (N + 1) ω) (r i) - Real.log (radialSigma N (r i)) - circularLogMean|}

/-- The union bound records exactly the number of radii. -/
theorem eventually_steinhausRadialLogarithmicFailure_le {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (steinhausRadialLogarithmicFailure N (r N)) ≤
        Fintype.card ι * (2 * steinhausOccupationConstant B K + 1) *
          (N : ℝ) ^ (-3 / 8 : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_steinhaus_logarithmic_concentration
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound K hK, hr] with N hN hrN
  let E : ι → Set (Fin (N + 1) → ℂ) := fun i => {ω | logarithmicTolerance N <
    |logCircleAverage (Polynomial.ofFn (N + 1) ω) (r N i) - Real.log (radialSigma N (r N i)) - circularLogMean|}
  have heq : steinhausRadialLogarithmicFailure N (r N) = ⋃ i, E i := by ext ω; simp [steinhausRadialLogarithmicFailure, E]
  rw [heq]
  calc
    _ ≤ ∑ i, (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, (2 * steinhausOccupationConstant B K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) :=
      Finset.sum_le_sum fun i _ => hN (r N i) (hrN i).1 (hrN i).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Actual finite-prefix failure probabilities are summable for every fixed
finite family of radii in a fixed `K/N` annulus. -/
theorem summable_steinhausRadialLogarithmicFailure {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    Summable (fun j : ℕ => (Measure.pi (fun _ : Fin (j ^ s + 1) => steinhausMeasure)).real
      (steinhausRadialLogarithmicFailure (j ^ s) (r (j ^ s)))) := by
  obtain ⟨B, _, hbound⟩ := eventually_steinhausRadialLogarithmicFailure_le K hK r hr
  have hsum := summable_logarithmic_failure_power s hs
    ((Fintype.card ι : ℝ) * (2 * steinhausOccupationConstant B K + 1))
  apply hsum.of_norm_bounded_eventually_nat
  have hs0 : 0 < s := by omega
  filter_upwards [(tendsto_pow_atTop (α := ℕ) hs0.ne').eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- The sparse logarithmic tolerance holds for every probe on one shared sequence. -/
theorem ae_eventually_steinhaus_sparse_radial_logarithmic_bound {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    ∀ᵐ ω ∂coefficientSequenceMeasure steinhausMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (polynomialPrefix ω (fun _ => 1) (j ^ s))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ s) := by
  have h := ae_eventually_indexed_coefficientPrefix_notMem steinhausMeasure (fun j => j ^ s)
    (fun j => steinhausRadialLogarithmicFailure (j ^ s) (r (j ^ s)))
    (summable_steinhausRadialLogarithmicFailure K hK r hr s hs)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro i
  have hi : ¬ logarithmicTolerance (j ^ s) <
      |logCircleAverage (Polynomial.ofFn (j ^ s + 1) (coefficientPrefix (j ^ s) ω))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| :=
    fun hh => hj ⟨i, hh⟩
  simpa only [coefficientPrefix_polynomial] using le_of_not_gt hi

/-- The four annular Jensen probes satisfy the same tolerance almost surely. -/
theorem ae_eventually_steinhaus_four_radial_logarithmic_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂coefficientSequenceMeasure steinhausMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix ω (fun _ => 1) (j ^ 8))
          (radialSecantRadii K (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (radialSecantRadii K (j ^ 8) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ 8) :=
  ae_eventually_steinhaus_sparse_radial_logarithmic_bound K hK (radialSecantRadii K)
    (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus hK N i) 8 (by norm_num)

end Erdos522

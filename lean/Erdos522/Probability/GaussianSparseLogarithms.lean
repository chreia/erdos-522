/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianConcentrationRate
import Erdos522.Probability.GaussianSequence
import Erdos522.Probability.SparseLogarithmicConcentration

/-!
# Sparse logarithmic averages for a Gaussian sequence

The polynomial concentration bound is summable along `j^s` for `3s > 8`.
Finite families of radial probes are handled by their exact union bound,
and Borel–Cantelli acts on prefixes of a single Gaussian coefficient sequence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace Erdos522

/-- Failure of a finite family of logarithmic-average estimates. -/
def gaussianRadialLogarithmicFailure {ι : Type*} (N : ℕ) (r : ι → ℝ) :
    Set (Fin (N + 1) → ℝ) :=
  {g | ∃ i, logarithmicTolerance N <
    |logCircleAverage (gaussianPolynomial N g) (r i) - Real.log (radialSigma N (r i)) - circularLogMean|}

/-- The exact finite-family union bound. -/
theorem eventually_gaussianRadialLogarithmicFailure_le {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∀ᶠ N : ℕ in atTop,
      (gaussianCoefficientMeasure (N + 1)).real (gaussianRadialLogarithmicFailure N (r N)) ≤
        Fintype.card ι * (2 * gaussianOccupationConstant K + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  filter_upwards [eventually_gaussian_logarithmic_concentration_power K hK, hr] with N hN hrN
  let E : ι → Set (Fin (N + 1) → ℝ) := fun i => {g | logarithmicTolerance N <
    |logCircleAverage (gaussianPolynomial N g) (r N i) - Real.log (radialSigma N (r N i)) - circularLogMean|}
  have heq : gaussianRadialLogarithmicFailure N (r N) = ⋃ i, E i := by
    ext g; simp [gaussianRadialLogarithmicFailure, E]
  rw [heq]
  calc
    _ ≤ ∑ i, (gaussianCoefficientMeasure (N + 1)).real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, (2 * gaussianOccupationConstant K + 2) * (N : ℝ) ^ (-3 / 8 : ℝ) :=
      Finset.sum_le_sum fun i _ => hN (r N i) (hrN i).1 (hrN i).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Finite Gaussian radial exceptions are summable along each admissible sparse sequence. -/
theorem summable_gaussianRadialLogarithmicFailure {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    Summable (fun j : ℕ => (gaussianCoefficientMeasure (j ^ s + 1)).real
      (gaussianRadialLogarithmicFailure (j ^ s) (r (j ^ s)))) := by
  have hbound := eventually_gaussianRadialLogarithmicFailure_le K hK r hr
  have hsum := summable_logarithmic_failure_power s hs
    ((Fintype.card ι : ℝ) * (2 * gaussianOccupationConstant K + 2))
  apply hsum.of_norm_bounded_eventually_nat
  have hs0 : 0 < s := by omega
  filter_upwards [(tendsto_pow_atTop (α := ℕ) hs0.ne').eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- The sparse logarithmic tolerance holds for every probe on one shared sequence. -/
theorem ae_eventually_gaussian_sparse_radial_logarithmic_bound {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (polynomialPrefix (fun k => (ω k : ℂ)) (fun _ => 1) (j ^ s))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ s) := by
  have h := ae_eventually_indexed_gaussianPrefix_notMem (fun j => j ^ s)
    (fun j => gaussianRadialLogarithmicFailure (j ^ s) (r (j ^ s)))
    (summable_gaussianRadialLogarithmicFailure K hK r hr s hs)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro i
  have hi : ¬ logarithmicTolerance (j ^ s) <
      |logCircleAverage (gaussianPolynomial (j ^ s) (gaussianPrefix (j ^ s) ω))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| :=
    fun hh => hj ⟨i, hh⟩
  simpa only [gaussianPrefix_polynomial] using le_of_not_gt hi

/-- The four annular Jensen probes satisfy the same tolerance almost surely. -/
theorem ae_eventually_gaussian_four_radial_logarithmic_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂gaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix (fun k => (ω k : ℂ)) (fun _ => 1) (j ^ 8))
          (radialSecantRadii K (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (radialSecantRadii K (j ^ 8) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ 8) :=
  ae_eventually_gaussian_sparse_radial_logarithmic_bound K hK (radialSecantRadii K)
    (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus hK N i) 8 (by norm_num)

end Erdos522

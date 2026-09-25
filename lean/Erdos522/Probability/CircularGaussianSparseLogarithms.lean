/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.CircularGaussianConcentrationRate
import Erdos522.Probability.CircularGaussianSequence
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
def circularGaussianRadialLogarithmicFailure {ι : Type*} (N : ℕ) (r : ι → ℝ) :
    Set (Fin (N + 1) → ℂ) :=
  {g | ∃ i, logarithmicTolerance N <
    |logCircleAverage (Polynomial.ofFn (N+1) g) (r i) - Real.log (radialSigma N (r i)) - circularLogMean|}

/-- The exact finite-family union bound. -/
theorem eventually_circularGaussianRadialLogarithmicFailure_le {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∀ᶠ N : ℕ in atTop,
      (Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).real (circularGaussianRadialLogarithmicFailure N (r N)) ≤
        Fintype.card ι * (2 * circularGaussianOccupationConstant K + 3) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  filter_upwards [eventually_circularGaussian_logarithmic_concentration_power K hK, hr] with N hN hrN
  let E : ι → Set (Fin (N + 1) → ℂ) := fun i => {g | logarithmicTolerance N <
    |logCircleAverage (Polynomial.ofFn (N+1) g) (r N i) - Real.log (radialSigma N (r N i)) - circularLogMean|}
  have heq : circularGaussianRadialLogarithmicFailure N (r N) = ⋃ i, E i := by
    ext g; simp [circularGaussianRadialLogarithmicFailure, E]
  rw [heq]
  calc
    _ ≤ ∑ i, (Measure.pi (fun _ : Fin (N+1) => circularComplexGaussian)).real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, (2 * circularGaussianOccupationConstant K + 3) * (N : ℝ) ^ (-3 / 8 : ℝ) :=
      Finset.sum_le_sum fun i _ => hN (r N i) (hrN i).1 (hrN i).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Finite Gaussian radial exceptions are summable along each admissible sparse sequence. -/
theorem summable_circularGaussianRadialLogarithmicFailure {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    Summable (fun j : ℕ => (Measure.pi (fun _ : Fin (j^s+1) => circularComplexGaussian)).real
      (circularGaussianRadialLogarithmicFailure (j ^ s) (r (j ^ s)))) := by
  have hbound := eventually_circularGaussianRadialLogarithmicFailure_le K hK r hr
  have hsum := summable_logarithmic_failure_power s hs
    ((Fintype.card ι : ℝ) * (2 * circularGaussianOccupationConstant K + 3))
  apply hsum.of_norm_bounded_eventually_nat
  have hs0 : 0 < s := by omega
  filter_upwards [(tendsto_pow_atTop (α := ℕ) hs0.ne').eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- The sparse logarithmic tolerance holds for every probe on one shared sequence. -/
theorem ae_eventually_circularGaussian_sparse_radial_logarithmic_bound {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (polynomialPrefix ω (fun _ => 1) (j ^ s))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ s) := by
  have h := ae_eventually_indexed_circularGaussianPrefix_notMem (fun j => j ^ s)
    (fun j => circularGaussianRadialLogarithmicFailure (j ^ s) (r (j ^ s)))
    (summable_circularGaussianRadialLogarithmicFailure K hK r hr s hs)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro i
  have hi : ¬ logarithmicTolerance (j ^ s) <
      |logCircleAverage (Polynomial.ofFn (j^s+1) (coefficientPrefix (j ^ s) ω))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| :=
    fun hh => hj ⟨i, hh⟩
  simpa only [coefficientPrefix_polynomial] using le_of_not_gt hi

/-- The four annular Jensen probes satisfy the same tolerance almost surely. -/
theorem ae_eventually_circularGaussian_four_radial_logarithmic_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂circularGaussianSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix ω (fun _ => 1) (j ^ 8))
          (radialSecantRadii K (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (radialSecantRadii K (j ^ 8) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ 8) :=
  ae_eventually_circularGaussian_sparse_radial_logarithmic_bound K hK (radialSecantRadii K)
    (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus hK N i) 8 (by norm_num)

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogarithmicConcentrationRate
import Erdos522.Probability.RademacherSequence
import Mathlib.Analysis.PSeries

/-!
# Sparse logarithmic control for one coin sequence

A finite collection of radii costs its cardinality in the probability bound.
Along polynomially sparse degrees, the bound is summable as soon as the degree
exponent is greater than `8/3`. All almost-sure statements concern prefixes of
one infinite sequence of signs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace Erdos522
open LogMoments

/-- A finite family of radial logarithmic deviations. -/
def radialLogarithmicFailure {ι : Type*} (N : ℕ) (r : ι → ℝ) : Set (SignVector N) :=
  {ω | ∃ i, logarithmicTolerance N <
    |logCircleAverage (rademacherPolynomial N ω) (r i) - Real.log (radialSigma N (r i)) - circularLogMean|}

/-- The union bound records exactly the number of radii. -/
theorem eventually_radialLogarithmicFailure_le {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      (signMeasure N).real (radialLogarithmicFailure N (r N)) ≤
        Fintype.card ι * (2 * rademacherOccupationConstant B K + 1) *
          (N : ℝ) ^ (-3 / 8 : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_rademacher_logarithmic_concentration hC hR
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound K hK, hr] with N hN hrN
  let E : ι → Set (SignVector N) := fun i => {ω | logarithmicTolerance N <
    |logCircleAverage (rademacherPolynomial N ω) (r N i) - Real.log (radialSigma N (r N i)) - circularLogMean|}
  have heq : radialLogarithmicFailure N (r N) = ⋃ i, E i := by ext ω; simp [radialLogarithmicFailure, E]
  rw [heq]
  calc
    _ ≤ ∑ i, (signMeasure N).real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, (2 * rademacherOccupationConstant B K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) :=
      Finset.sum_le_sum fun i _ => hN (r N i) (hrN i).1 (hrN i).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The logarithmic-concentration failure power is summable above the sharp
subsequence threshold supplied by its exponent. -/
theorem summable_logarithmic_failure_power (s : ℕ) (hs : 8 < 3 * s) (B : ℝ) :
    Summable (fun j : ℕ => B * ((j ^ s : ℕ) : ℝ) ^ (-3 / 8 : ℝ)) := by
  have hexponent : (s : ℝ) * (-3 / 8 : ℝ) < -1 := by
    have hsr : (8 : ℝ) < 3 * s := by exact_mod_cast hs
    linarith
  apply ((Real.summable_nat_rpow.mpr hexponent).mul_left B).congr
  intro j
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg j)]

/-- Actual finite-prefix failure probabilities are summable for every fixed
finite family of radii in a fixed `K/N` annulus. -/
theorem summable_radialLogarithmicFailure {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    Summable (fun j : ℕ => (signMeasure (j ^ s)).real
      (radialLogarithmicFailure (j ^ s) (r (j ^ s)))) := by
  obtain ⟨B, _, hbound⟩ := eventually_radialLogarithmicFailure_le hC hR K hK r hr
  have hsum := summable_logarithmic_failure_power s hs
    ((Fintype.card ι : ℝ) * (2 * rademacherOccupationConstant B K + 1))
  apply hsum.of_norm_bounded_eventually_nat
  have hs0 : 0 < s := by omega
  filter_upwards [(tendsto_pow_atTop (α := ℕ) hs0.ne').eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- Simultaneous sparse logarithmic control on one fixed infinite sign sequence. -/
theorem ae_eventually_sparse_radial_logarithmic_bound {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (r : ℕ → ι → ℝ)
    (hr : ∀ᶠ N : ℕ in atTop, ∀ i, 1 - K / N ≤ r N i ∧ r N i ≤ 1 + K / N)
    (s : ℕ) (hs : 8 < 3 * s) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i,
      |logCircleAverage (polynomialPrefix (fun k => sign (ω k)) (fun _ => 1) (j ^ s))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ s) := by
  have h := ae_eventually_rademacherPrefix_notMem (fun j => j ^ s)
    (fun N => radialLogarithmicFailure N (r N))
    (summable_radialLogarithmicFailure hC hR K hK r hr s hs)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with j hj
  intro i
  have hi : ¬ logarithmicTolerance (j ^ s) <
      |logCircleAverage (rademacherPolynomial (j ^ s) (rademacherPrefix (j ^ s) ω))
          (r (j ^ s) i) - Real.log (radialSigma (j ^ s) (r (j ^ s) i)) - circularLogMean| :=
    fun hh => hj ⟨i, hh⟩
  simpa only [rademacherPrefix_polynomial] using le_of_not_gt hi

/-- The four radii used by the annular Jensen secants. -/
def radialSecantRadii (K : ℝ) (N : ℕ) (i : Fin 4) : ℝ :=
  1 + ![-K, -K / 2, K / 2, K] i / N

theorem radialSecantRadii_mem_annulus {K : ℝ} (hK : 0 ≤ K) (N : ℕ) (i : Fin 4) :
    1 - K / N ≤ radialSecantRadii K N i ∧ radialSecantRadii K N i ≤ 1 + K / N := by
  have hd : 0 ≤ K / N := div_nonneg hK (Nat.cast_nonneg N)
  have hh : K / 2 / (N : ℝ) = (K / N) / 2 := by ring
  fin_cases i <;> simp [radialSecantRadii, neg_div, hh] <;> (try constructor) <;> linarith

/-- Four radial probes cost exactly four one-point probabilities. -/
theorem eventually_four_radial_logarithmic_failure_le {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (K : ℝ) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      (signMeasure N).real (radialLogarithmicFailure N (radialSecantRadii K N)) ≤
        4 * (2 * rademacherOccupationConstant B K + 1) * (N : ℝ) ^ (-3 / 8 : ℝ) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    eventually_radialLogarithmicFailure_le hC hR K hK (radialSecantRadii K)
      (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus hK N i)

/-- The four Jensen radii satisfy the manuscript tolerance almost surely along `j^8`. -/
theorem ae_eventually_four_radial_logarithmic_bound {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix (fun k => sign (ω k)) (fun _ => 1) (j ^ 8))
          (radialSecantRadii K (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (radialSecantRadii K (j ^ 8) i)) - circularLogMean| ≤
        logarithmicTolerance (j ^ 8) :=
  ae_eventually_sparse_radial_logarithmic_bound hC hR K hK (radialSecantRadii K)
    (Filter.Eventually.of_forall fun N i => radialSecantRadii_mem_annulus hK N i) 8 (by norm_num)

end Erdos522

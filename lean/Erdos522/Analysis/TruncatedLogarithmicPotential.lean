/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.LogarithmicPotential
import Mathlib.MeasureTheory.Order.Lattice

/-!
# The largest logarithmic potentials

The sum of the largest `d` negative logarithmic potentials is controlled by
clipping every potential at a common height. The part below the height costs
only `d` times that height; all the excess tails together have exponentially
small integral. This retains the effective degree in a measurable-set bound.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Erdos522

/-- Collections of at most `d` labels among `N` given points. -/
def logarithmicSubsets (N d : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun s => s.card ≤ d)

theorem logarithmicSubsets_nonempty (N d : ℕ) : (logarithmicSubsets N d).Nonempty := by
  exact ⟨∅, by simp [logarithmicSubsets]⟩

/-- The sum of the largest `d` nonnegative logarithmic potentials. Labels may
repeat, so each zero contributes according to its multiplicity. -/
def largestLogarithmicPotential {N : ℕ} (w : Fin N → ℂ) (d : ℕ) (x : ℝ) : ℝ :=
  (logarithmicSubsets N d).sup' (logarithmicSubsets_nonempty N d)
    (fun s => ∑ i ∈ s, negativeLogPotential (w i) x)

theorem measurable_largestLogarithmicPotential {N : ℕ} (w : Fin N → ℂ) (d : ℕ) :
    Measurable (largestLogarithmicPotential w d) := by
  have h := Finset.measurable_sup' (logarithmicSubsets_nonempty N d)
    (f := fun s x => ∑ i ∈ s, negativeLogPotential (w i) x)
    (fun s _ => Finset.measurable_sum s
      (fun i _ => measurable_negativeLogPotential (w i)))
  have heq : largestLogarithmicPotential w d =
      (logarithmicSubsets N d).sup' (logarithmicSubsets_nonempty N d)
        (fun s x => ∑ i ∈ s, negativeLogPotential (w i) x) := by
    funext x
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  exact h

theorem sum_negativeLogPotential_le_largest {N : ℕ} (w : Fin N → ℂ) (d : ℕ)
    (s : Finset (Fin N)) (hs : s.card ≤ d) (x : ℝ) :
    (∑ i ∈ s, negativeLogPotential (w i) x) ≤ largestLogarithmicPotential w d x := by
  change _ ≤ (logarithmicSubsets N d).sup' _ _
  apply Finset.le_sup' (fun t => ∑ i ∈ t, negativeLogPotential (w i) x)
  simp [logarithmicSubsets, hs]

theorem largestLogarithmicPotential_nonneg {N : ℕ} (w : Fin N → ℂ) (d : ℕ) (x : ℝ) :
    0 ≤ largestLogarithmicPotential w d x := by
  simpa using sum_negativeLogPotential_le_largest w d ∅ (by simp) x

/-- Clipping at height `T` costs `dT` plus the sum of all excess tails. -/
theorem largestLogarithmicPotential_le_height_add_tails {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    largestLogarithmicPotential w d x ≤
      d * T + ∑ i, negativeLogPotentialTail (w i) T x := by
  apply Finset.sup'_le
  intro s hs
  have hsd : s.card ≤ d := (Finset.mem_filter.mp hs).2
  have hsdR : (s.card : ℝ) ≤ d := by exact_mod_cast hsd
  calc
    (∑ i ∈ s, negativeLogPotential (w i) x) ≤
        ∑ i ∈ s, (T + negativeLogPotentialTail (w i) T x) :=
      Finset.sum_le_sum fun i _ => negativeLogPotential_le_height_add_tail (w i) hT x
    _ = s.card * T + ∑ i ∈ s, negativeLogPotentialTail (w i) T x := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ d * T + ∑ i, negativeLogPotentialTail (w i) T x := by
      apply add_le_add (mul_le_mul_of_nonneg_right hsdR hT)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact le_max_right _ _

/-- The largest-potential integral at any clipping height, on a finite real set. -/
theorem integrable_largestLogarithmicPotential_and_integral_le_height {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (largestLogarithmicPotential w d) E ∧
      (∫ x in E, largestLogarithmicPotential w d x) ≤
        volume.real E * (d * T) + 2 * N * Real.exp (-T) := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hfinite
  have htail (i : Fin N) := integrable_negativeLogPotentialTail_and_integral_le (w i) E T
  have hsum : IntegrableOn (fun x => ∑ i, negativeLogPotentialTail (w i) T x) E :=
    integrable_finsetSum _ (fun i _ => (htail i).1)
  have hdom : IntegrableOn (fun x => d * T + ∑ i, negativeLogPotentialTail (w i) T x) E :=
    (integrable_const _).add hsum
  have hint : IntegrableOn (largestLogarithmicPotential w d) E :=
    hdom.mono_nonneg (measurable_largestLogarithmicPotential w d).aestronglyMeasurable
      (ae_of_all _ (largestLogarithmicPotential_nonneg w d))
      (ae_of_all _ (largestLogarithmicPotential_le_height_add_tails w d hT))
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x in E, d * T + ∑ i, negativeLogPotentialTail (w i) T x :=
      integral_mono hint hdom (largestLogarithmicPotential_le_height_add_tails w d hT)
    _ = volume.real E * (d * T) + ∑ i, ∫ x in E, negativeLogPotentialTail (w i) T x := by
      rw [integral_add (integrable_const _) hsum, setIntegral_const, smul_eq_mul,
        integral_finsetSum _ (fun i _ => (htail i).1)]
    _ ≤ volume.real E * (d * T) + ∑ _i : Fin N, 2 * Real.exp (-T) :=
      add_le_add_right (Finset.sum_le_sum fun i _ => (htail i).2) _
    _ = _ := by simp; ring

/-- Optimizing the clipping height preserves the effective number `d` of
nearby zeros, even when the full zero set is larger. -/
theorem integral_largestLogarithmicPotential_le {N d : ℕ}
    (w : Fin N → ℂ) (hd : 0 < d) (hdN : d ≤ N)
    (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 2) :
    (∫ x in E, largestLogarithmicPotential w d x) ≤
      volume.real E * d * (1 + Real.log (2 * N / (d * volume.real E))) := by
  let α := volume.real E
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hdN
  have hdNR : (d : ℝ) ≤ N := by exact_mod_cast hdN
  have hα : 0 < α := hpos
  have hden : 0 < (d : ℝ) * α := mul_pos hdR hα
  have hratio : 0 < 2 * (N : ℝ) / (d * α) := by positivity
  have hT : 0 ≤ Real.log (2 * (N : ℝ) / (d * α)) := by
    apply Real.log_nonneg
    apply (one_le_div hden).mpr
    nlinarith
  have h := (integrable_largestLogarithmicPotential_and_integral_le_height w d E hfinite hT).2
  have heq : 2 * (N : ℝ) * Real.exp (-Real.log (2 * N / (d * α))) = d * α := by
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  rw [heq] at h
  convert h using 1
  dsimp [α]
  ring

/-- A convenient additive form separates total zero count from effective degree.
Only `d` multiplies the logarithm of inverse set length. -/
theorem integral_largestLogarithmicPotential_le_count_add_log {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ)
    (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 1) :
    (∫ x in E, largestLogarithmicPotential w d x) ≤
      volume.real E * (2 * N + d * Real.log (1 / volume.real E)) := by
  have hT : 0 ≤ Real.log (1 / volume.real E) :=
    Real.log_nonneg ((one_le_div hpos).mpr hle)
  have h := (integrable_largestLogarithmicPotential_and_integral_le_height
    w d E hfinite hT).2
  have heq : Real.exp (-Real.log (1 / volume.real E)) = volume.real E := by
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  rw [heq] at h
  convert h using 1
  ring

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ClippedSums
import Erdos522.Analysis.TruncatedLogarithmicPotential
import Erdos522.Analysis.GeometricMean

/-!
# Measurable restriction from effective logarithmic potentials

A clipped-sum bound removes all but the effective number of nearby zeros.
Integrating the remaining largest potentials keeps that number as the
exponent of inverse set length in the geometric-mean restriction estimate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Erdos522

/-- A bound on every clipped sum leaves only the largest `d` potentials.
If fewer than `d` zeros are present, all potentials are retained. -/
theorem sum_negativeLogPotential_le_largest_add {N d : ℕ}
    (w : Fin N → ℂ) (hd : 0 < d) {H : ℝ} (hH : 0 ≤ H) (x : ℝ)
    (hclip : ∀ T : ℝ, 0 ≤ T →
      (∑ i, min T (negativeLogPotential (w i) x)) ≤ H + d * T) :
    (∑ i, negativeLogPotential (w i) x) ≤ H + largestLogarithmicPotential w d x := by
  by_cases hdN : d ≤ N
  · obtain ⟨s, _, hs, hsum⟩ := sum_le_largest_subset_add_of_clipped_bound
      Finset.univ (fun i => negativeLogPotential (w i) x)
      (fun _ _ => le_max_right _ _) hd (by simpa using hdN) hclip
    exact hsum.trans (add_le_add (le_refl H)
      (sum_negativeLogPotential_le_largest w d s hs.le x))
  · have hNd : N ≤ d := by omega
    exact (sum_negativeLogPotential_le_largest w d Finset.univ (by simpa using hNd) x).trans
      (le_add_of_nonneg_left hH)

/-- Two-sided logarithmic bounds by an integrable potential imply
logarithmic integrability, including the almost-everywhere formulation. -/
theorem integrable_log_norm_of_potential_bounds {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (f : ℝ → ℂ) (hf : Measurable f) (A S : ℝ)
    (hupper : ∀ᵐ x ∂volume.restrict E, Real.log ‖f x‖ ≤ A)
    (hdefect : ∀ᵐ x ∂volume.restrict E,
      A - Real.log ‖f x‖ ≤ S + largestLogarithmicPotential w d x) :
    IntegrableOn (fun x => Real.log ‖f x‖) E := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hfinite
  have hpot := (integrable_largestLogarithmicPotential_and_integral_le_height
    w d E hfinite (T := 0) le_rfl).1
  have hdom : IntegrableOn (fun x => |A| + |S| + largestLogarithmicPotential w d x) E :=
    (integrable_const _).add hpot
  apply hdom.mono' hf.norm.log.aestronglyMeasurable
  filter_upwards [hupper, hdefect] with x hu hd
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [le_abs_self S, neg_abs_le A]
  · linarith [le_abs_self A, abs_nonneg S, largestLogarithmicPotential_nonneg w d x]

/-- A pointwise effective-potential bound gives its measurable logarithmic
restriction inequality with explicit total-count cost. -/
theorem logarithmic_restriction_of_potential_bound {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 1)
    (f : ℝ → ℂ) (hf : Measurable f) (A S : ℝ)
    (hupper : ∀ᵐ x ∂volume.restrict E, Real.log ‖f x‖ ≤ A)
    (hdefect : ∀ᵐ x ∂volume.restrict E,
      A - Real.log ‖f x‖ ≤ S + largestLogarithmicPotential w d x) :
    A ≤ (⨍ x in E, Real.log ‖f x‖) + S + 2 * N + d * Real.log (1 / volume.real E) := by
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hfinite
  have hlog := integrable_log_norm_of_potential_bounds w d E hfinite f hf A S hupper hdefect
  have hpot := (integrable_largestLogarithmicPotential_and_integral_le_height
    w d E hfinite (T := 0) le_rfl).1
  have h := integral_mono_ae ((integrable_const A).sub hlog)
    ((integrable_const S).add hpot) hdefect
  change (∫ x in E, A - Real.log ‖f x‖) ≤
    ∫ x in E, S + largestLogarithmicPotential w d x at h
  rw [integral_sub (integrable_const A) hlog, integral_add (integrable_const S) hpot,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul] at h
  have hp := integral_largestLogarithmicPotential_le_count_add_log w d E hfinite hpos hle
  have hbound : volume.real E * A ≤ (∫ x in E, Real.log ‖f x‖) +
      volume.real E * (S + 2 * N + d * Real.log (1 / volume.real E)) := by
    nlinarith
  rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ]
  have hdiv : A ≤ ((∫ x in E, Real.log ‖f x‖) +
      volume.real E * (S + 2 * N + d * Real.log (1 / volume.real E))) / volume.real E :=
    (le_div_iff₀ hpos).mpr (by nlinarith [hbound])
  convert hdiv using 1
  field_simp
  ring

/-- Exponentiation yields geometric-mean restriction with degree `d`.
The dependence on the total number of zeros occurs only exponentially. -/
theorem geometric_restriction_of_potential_bound {N : ℕ}
    (w : Fin N → ℂ) (d : ℕ) (E : Set ℝ) (hfinite : volume E ≠ ∞)
    (hpos : 0 < volume.real E) (hle : volume.real E ≤ 1)
    (f : ℝ → ℂ) (hf : Measurable f) (A S : ℝ)
    (hupper : ∀ᵐ x ∂volume.restrict E, Real.log ‖f x‖ ≤ A)
    (hdefect : ∀ᵐ x ∂volume.restrict E,
      A - Real.log ‖f x‖ ≤ S + largestLogarithmicPotential w d x) :
    Real.exp A ≤ Real.exp (S + 2 * N) * (1 / volume.real E) ^ d *
      geometricMean (volume.restrict E) f := by
  have h := Real.exp_le_exp.mpr
    (logarithmic_restriction_of_potential_bound w d E hfinite hpos hle f hf A S hupper hdefect)
  have hexp : Real.exp ((d : ℝ) * Real.log (1 / volume.real E)) =
      (1 / volume.real E) ^ d := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have heq : (⨍ x in E, Real.log ‖f x‖) + S + 2 * N + d * Real.log (1 / volume.real E) =
      (S + 2 * N) + d * Real.log (1 / volume.real E) + (⨍ x in E, Real.log ‖f x‖) := by ring
  rw [heq, Real.exp_add, Real.exp_add, hexp] at h
  exact h

end Erdos522

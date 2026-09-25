/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SublevelCrossingBound
import Erdos522.Limits.SublevelCrossingScales

/-!
# Summable control of nearby-circle sublevel components

For any finite family of circles with displacement `o(1/N)`, a deterministic
vanishing envelope controls the fraction of roots in crossing components.
The exceptional probabilities are summable along the eighth-power degrees.
Sublevel thresholds may vary with degree below any fixed block-tail envelope.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Erdos522
open LogMoments

/-- At each fixed annular width, exceedances of the crossing envelope have
summable probabilities for any finite collection of nearby circles. -/
theorem summable_sublevel_crossing_exceedances {ι : Type*} [Finite ι]
    (K : ℕ) (K₀ : ℝ) (a : ℕ → ℝ)
    (ha : ∀ᶠ j : ℕ in atTop,
      a (j ^ 8) ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
    (r : ℕ → ι → ℝ)
    (hr : ∀ i, Tendsto (fun N : ℕ => (N : ℝ) * (r N i - 1)) atTop (𝓝 0)) :
    Summable (fun j : ℕ => (signMeasure (j ^ 8)).real {v | ∃ i,
      sublevelCrossingEnvelope K (j ^ 8) <
        (sublevelComponentZeroCount (rademacherPolynomial (j ^ 8) v)
          (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)}) := by
  apply (summable_sublevelCrossingFailure K).of_norm_bounded_eventually_nat
  have hdegree := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  have hsize := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hdegree).eventually_gt_atTop
    (2 * max ((K : ℝ) + 1) (reciprocalProbeWidth K))
  filter_upwards [ha, hdegree.eventually_ge_atTop 1, hsize,
    eventually_eighth_power_sublevel_crossing_scales_finite ((K : ℝ) + 1) K₀
      (reciprocalProbeWidth_pos K) r hr] with j haj hN hj hscale
  change 2 * max ((K : ℝ) + 1) (reciprocalProbeWidth K) < ((j ^ 8 : ℕ) : ℝ) at hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  apply measureReal_mono (μ := signMeasure (j ^ 8)) _ (measure_ne_top _ _)
  intro v hv
  by_contra hgood
  obtain ⟨i, hi⟩ := hv
  obtain ⟨hapos, hdpos, hbudget, hradius, hwindow⟩ := hscale
  have houter : 2 * ((K : ℝ) + 1) < ((j ^ 8 : ℕ) : ℝ) := by
    linarith [le_max_left ((K : ℝ) + 1) (reciprocalProbeWidth K)]
  have hinner : 2 * reciprocalProbeWidth K < ((j ^ 8 : ℕ) : ℝ) := by
    linarith [le_max_right ((K : ℝ) + 1) (reciprocalProbeWidth K)]
  have hfinite := sublevel_crossing_fraction_le_envelope K (j ^ 8) v
    (by omega) houter hinner hapos hdpos hbudget hradius (hwindow i) hgood
  have hmono :
      (sublevelComponentZeroCount (rademacherPolynomial (j ^ 8) v)
        (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ) ≤
      (sublevelComponentZeroCount (rademacherPolynomial (j ^ 8) v)
        (TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
        (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ) :=
    div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (sublevelComponentZeroCount_mono (rademacherPolynomial (j ^ 8) v)
        (r := r (j ^ 8) i) haj)) (Nat.cast_nonneg (j ^ 8))
  exact hi.not_ge (hmono.trans hfinite)

/-- One deterministic vanishing envelope and one summable exceptional sequence
control every selected nearby circle on the original infinite coin space. -/
theorem exists_summable_sublevel_crossing_envelope {ι : Type*} [Finite ι]
    (K₀ : ℝ) (a : ℕ → ℝ)
    (ha : ∀ᶠ j : ℕ in atTop,
      a (j ^ 8) ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
    (r : ℕ → ι → ℝ)
    (hr : ∀ i, Tendsto (fun N : ℕ => (N : ℝ) * (r N i - 1)) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 ≤ ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      Summable (fun j : ℕ => rademacherSequenceMeasure.real {ω | ∃ i,
        ε j < (sublevelComponentZeroCount
          (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
          (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)}) := by
  let E (K j : ℕ) : Set (SignVector (j ^ 8)) := {v | ∃ i,
    sublevelCrossingEnvelope K (j ^ 8) <
      (sublevelComponentZeroCount (rademacherPolynomial (j ^ 8) v)
        (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)}
  have hp (K : ℕ) : (∑' j, signMeasure (j ^ 8) (E K j)) ≠ ∞ := by
    have hs := summable_sublevel_crossing_exceedances K K₀ a ha r hr
    simpa only [E, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hs.tsum_ofReal_ne_top
  obtain ⟨s, _, hlimit, hsum⟩ := exists_summable_sublevel_crossing_diagonal hp
  refine ⟨fun j => |sublevelCrossingEnvelope (s j) (j ^ 8)|,
    fun j => abs_nonneg _, by simpa only [abs_zero] using hlimit.abs, ?_⟩
  have hselected := ENNReal.summable_toReal hsum
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hselected
  intro j
  have hsub : {ω : RademacherSequence | ∃ i,
      |sublevelCrossingEnvelope (s j) (j ^ 8)| <
        (sublevelComponentZeroCount
          (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
          (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)} ⊆
      rademacherPrefix (j ^ 8) ⁻¹' E (s j) j := by
    intro ω hω
    obtain ⟨i, hi⟩ := hω
    exact ⟨i, (le_abs_self _).trans_lt hi⟩
  have h := measureReal_mono (μ := rademacherSequenceMeasure) hsub
  rw [measureReal_rademacherPrefix_preimage] at h
  exact h

/-- Crossing-component root fractions tend to zero almost surely, simultaneously
for the finite family of target circles. -/
theorem ae_sublevel_crossing_fractions_tendsto_zero {ι : Type*} [Finite ι]
    (K₀ : ℝ) (a : ℕ → ℝ)
    (ha : ∀ᶠ j : ℕ in atTop,
      a (j ^ 8) ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀)
    (r : ℕ → ι → ℝ)
    (hr : ∀ i, Tendsto (fun N : ℕ => (N : ℝ) * (r N i - 1)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ i,
      Tendsto (fun j : ℕ => (sublevelComponentZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)) atTop (𝓝 0) := by
  obtain ⟨ε, _, hε, hsum⟩ := exists_summable_sublevel_crossing_envelope K₀ a ha r hr
  have hfinite : (∑' j, rademacherSequenceMeasure {ω | ∃ i,
      ε j < (sublevelComponentZeroCount
        (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω))
        (a (j ^ 8)) (r (j ^ 8) i) : ℝ) / (j ^ 8 : ℕ)}) ≠ ∞ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsum.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  intro i
  apply squeeze_zero' (Eventually.of_forall fun j =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hε
  filter_upwards [hω] with j hj
  exact le_of_not_gt (fun hi => hj ⟨i, hi⟩)

end Erdos522

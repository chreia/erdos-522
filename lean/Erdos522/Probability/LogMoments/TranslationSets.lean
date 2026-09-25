/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SmallShifts
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Measure of intersections of angular translates

Finite intersections retain nearly all the measure of a measurable set when
all their angular translations are small. This supplies the integration sets
for normalized small-shift relations.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology symmDiff

namespace Erdos522.LogMoments

/-- The loss from a finite intersection is bounded by the sum of the individual losses. -/
theorem measureReal_sdiff_iInter_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (F : ι → Set Ω) :
    μ.real (E \ ⋂ j, F j) ≤ ∑ j, μ.real (E \ F j) := by
  classical
  rw [Set.sdiff_iInter]
  exact measureReal_iUnion_fintype_le _

/-- A finite intersection has at least the original measure minus all the losses. -/
theorem measureReal_iInter_ge {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (F : ι → Set Ω) :
    μ.real E - ∑ j, μ.real (E \ F j) ≤ μ.real (⋂ j, F j) := by
  have h₁ := measureReal_sdiff_iInter_le μ E F
  have h₂ := le_measureReal_sdiff (μ := μ) (s₁ := E) (s₂ := ⋂ j, F j)
  linarith

/-- Small losses under each angular shift leave at least half the original measure. -/
theorem half_measure_le_shiftIntersection {N n : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (t : AddCircle (1 : ℝ))
    (hsmall : ∀ j : Fin (n + 1),
      (fourierMeasure N).real (E \ angularTranslation N (j.val • t) ⁻¹' E) ≤
        (fourierMeasure N).real E / (2 * ((n : ℝ) + 1))) :
    (fourierMeasure N).real E / 2 ≤ (fourierMeasure N).real (shiftIntersection E n t) := by
  have hsum : (∑ j : Fin (n + 1),
      (fourierMeasure N).real (E \ angularTranslation N (j.val • t) ⁻¹' E)) ≤
        (fourierMeasure N).real E / 2 := by
    calc
      _ ≤ ∑ _j : Fin (n + 1), (fourierMeasure N).real E / (2 * ((n : ℝ) + 1)) :=
        Finset.sum_le_sum (fun j _ => hsmall j)
      _ = _ := by simp; field_simp
  have h := measureReal_iInter_ge (fourierMeasure N) E
    (fun j : Fin (n + 1) => angularTranslation N (j.val • t) ⁻¹' E)
  change _ ≤ (fourierMeasure N).real (⋂ j : Fin (n + 1),
    angularTranslation N (j.val • t) ⁻¹' E)
  linarith

/-- Angular translation as a continuous self-map of the joint space. -/
def angularContinuousMap (N : ℕ) (t : AddCircle (1 : ℝ)) :
    C(SignVector N × AddCircle (1 : ℝ), SignVector N × AddCircle (1 : ℝ)) :=
  ⟨fun q => (q.1, q.2 + t), by fun_prop⟩

theorem continuous_angularContinuousMap (N : ℕ) : Continuous (angularContinuousMap N) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : AddCircle (1 : ℝ) × (SignVector N × AddCircle (1 : ℝ)) =>
    (p.2.1, p.2.2 + p.1))
  fun_prop

/-- A measurable set is continuous in measure under angular translation. -/
theorem tendsto_measure_symmDiff_angularTranslation {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E) :
    Tendsto (fun t : AddCircle (1 : ℝ) =>
      fourierMeasure N ((angularTranslation N t ⁻¹' E) ∆ E)) (𝓝 0) (𝓝 0) := by
  have h := tendsto_measure_symmDiff_preimage_nhds_zero
    ((continuous_angularContinuousMap N).tendsto 0)
    (Filter.Eventually.of_forall (measurePreserving_angularTranslation N))
    (measurePreserving_angularTranslation N 0) hE.nullMeasurableSet (measure_ne_top _ _)
  change Tendsto (fun t : AddCircle (1 : ℝ) =>
    fourierMeasure N ((angularTranslation N t ⁻¹' E) ∆
      (angularTranslation N 0 ⁻¹' E))) (𝓝 0) (𝓝 0) at h
  have hz : angularTranslation N 0 ⁻¹' E = E := by
    ext q
    simp
  rwa [hz] at h

/-- The real-valued measure of the symmetric difference tends to zero as well. -/
theorem tendsto_measureReal_symmDiff_angularTranslation {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E) :
    Tendsto (fun t : AddCircle (1 : ℝ) =>
      (fourierMeasure N).real ((angularTranslation N t ⁻¹' E) ∆ E)) (𝓝 0) (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero, Measure.real] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp
      (tendsto_measure_symmDiff_angularTranslation hE)

/-- All finitely many shifts of a measurable positive-measure set retain half its measure
    throughout a neighborhood of the identity. -/
theorem eventually_half_measure_le_shiftIntersection {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (n : ℕ) :
    ∀ᶠ t : AddCircle (1 : ℝ) in 𝓝 0,
      (fourierMeasure N).real E / 2 ≤ (fourierMeasure N).real (shiftIntersection E n t) := by
  have εpos : 0 < (fourierMeasure N).real E / (2 * ((n : ℝ) + 1)) := by positivity
  have hj (j : Fin (n + 1)) : ∀ᶠ t : AddCircle (1 : ℝ) in 𝓝 0,
      (fourierMeasure N).real ((angularTranslation N (j.val • t) ⁻¹' E) ∆ E) <
        (fourierMeasure N).real E / (2 * ((n : ℝ) + 1)) := by
    have ht : Tendsto (fun t : AddCircle (1 : ℝ) => j.val • t) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : AddCircle (1 : ℝ) => j.val • t) := by fun_prop
      simpa using hc.tendsto (0 : AddCircle (1 : ℝ))
    exact ((tendsto_measureReal_symmDiff_angularTranslation hE).comp ht).eventually
      (gt_mem_nhds εpos)
  filter_upwards [Filter.eventually_all.mpr hj] with t ht
  apply half_measure_le_shiftIntersection
  intro j
  exact (measureReal_mono (fun _ hq => Or.inr hq)).trans (ht j).le

/-- A real positive interval of shift parameters works simultaneously for all the translates. -/
theorem exists_shift_radius {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (n : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t < τ →
      (fourierMeasure N).real E / 2 ≤
        (fourierMeasure N).real (shiftIntersection E n (t : AddCircle (1 : ℝ))) := by
  have hc : Continuous (fun t : ℝ => (t : AddCircle (1 : ℝ))) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (t : AddCircle (1 : ℝ))) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  obtain ⟨τ, hτ, hball⟩ := Metric.eventually_nhds_iff.mp
    (ht.eventually (eventually_half_measure_le_shiftIntersection hE hpos n))
  refine ⟨τ, hτ, fun t ht0 htτ => hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos ht0] using htτ

end Erdos522.LogMoments

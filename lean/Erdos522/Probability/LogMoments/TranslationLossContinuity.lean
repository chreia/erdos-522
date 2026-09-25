/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.TranslationSets
import Erdos522.Probability.LogMoments.AngularSections
import Erdos522.Analysis.FirstCrossing

/-!
# Continuity and first crossing of angular translation loss

The mass gained by translating a measurable event varies continuously with
the angular shift. A first crossing therefore selects a positive shift scale
with controlled loss at every smaller nonnegative shift.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology symmDiff
namespace Erdos522.LogMoments

/-- Symmetric difference controls the change of a finite set measure. -/
theorem abs_measureReal_sub_le_symmDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have hab := le_measureReal_sdiff (μ := μ) (s₁ := A) (s₂ := B)
  have hba := le_measureReal_sdiff (μ := μ) (s₁ := B) (s₂ := A)
  have ha : μ.real (A \ B) ≤ μ.real (A ∆ B) := measureReal_mono (fun _ hx => Or.inl hx)
  have hb : μ.real (B \ A) ≤ μ.real (A ∆ B) := measureReal_mono (fun _ hx => Or.inr hx)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_angularTranslationLoss_sub_le {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (s t : AddCircle (1 : ℝ)) :
    |angularTranslationLoss E s - angularTranslationLoss E t| ≤
      (fourierMeasure N).real ((angularTranslation N s ⁻¹' E) ∆
        (angularTranslation N t ⁻¹' E)) := by
  apply (abs_measureReal_sub_le_symmDiff (fourierMeasure N) _ _).trans
  apply measureReal_mono ?_ (by finiteness)
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.1.1, fun ht => hx.2 ⟨ht, hx.1.2⟩⟩
  · exact Or.inr ⟨hx.1.1, fun hs => hx.2 ⟨hs, hx.1.2⟩⟩

/-- Angular translation loss is continuous for every measurable event. -/
theorem continuous_angularTranslationLoss {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E) :
    Continuous (angularTranslationLoss E) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := tendsto_measure_symmDiff_preimage_nhds_zero
    ((continuous_angularContinuousMap N).tendsto t)
    (Filter.Eventually.of_forall (measurePreserving_angularTranslation N))
    (measurePreserving_angularTranslation N t) hE.nullMeasurableSet (measure_ne_top _ _)
  change Tendsto (fun s : AddCircle (1 : ℝ) =>
    fourierMeasure N ((angularTranslation N s ⁻¹' E) ∆
      (angularTranslation N t ⁻¹' E))) (𝓝 t) (𝓝 0) at h
  have hr : Tendsto (fun s : AddCircle (1 : ℝ) =>
      (fourierMeasure N).real ((angularTranslation N s ⁻¹' E) ∆
        (angularTranslation N t ⁻¹' E))) (𝓝 t) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero, Measure.real] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun s => by simpa only [Real.dist_eq] using abs_angularTranslationLoss_sub_le E s t) hr

@[simp] theorem angularTranslationLoss_zero {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) : angularTranslationLoss E 0 = 0 := by
  have heq : angularTranslation N 0 ⁻¹' E = E := by ext x; simp
  simp only [angularTranslationLoss, heq, sdiff_self, measureReal_empty]

/-- A loss reached at a nonnegative real shift is first attained at a positive
shift, and all smaller nonnegative shifts have strictly smaller loss. -/
theorem exists_first_angular_loss {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T)
    (hreach : c ≤ angularTranslationLoss E (T : AddCircle (1 : ℝ))) :
    ∃ t ∈ Ioc (0 : ℝ) T, angularTranslationLoss E (t : AddCircle (1 : ℝ)) = c ∧
      ∀ s ∈ Ico (0 : ℝ) t, angularTranslationLoss E (s : AddCircle (1 : ℝ)) < c := by
  apply exists_first_crossing ((continuous_angularTranslationLoss hE).comp (by fun_prop)) hT
  · simpa only [Function.comp_apply, AddCircle.coe_zero, angularTranslationLoss_zero] using hc
  · exact hreach

end Erdos522.LogMoments

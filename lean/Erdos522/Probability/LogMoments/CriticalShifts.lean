/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.TranslationLossContinuity
import Erdos522.Probability.LogMoments.QuantitativeShifts
import Erdos522.Probability.LogMoments.PropagationOrder

/-!
# Choosing a shift with definite measure growth

The first crossing of angular translation loss supplies both the measure gain
needed for spreading and the half-measure intersections needed for normalized
small-shift relations.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Angular translation removes exactly as much event mass as it adds. -/
theorem measure_removed_eq_angularTranslationLoss {N : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    (t : AddCircle (1 : ℝ)) :
    (fourierMeasure N).real (E \ angularTranslation N t ⁻¹' E) =
      angularTranslationLoss E t := by
  have hp := hE.preimage (angularTranslation N t).measurable
  have heq : (fourierMeasure N).real (angularTranslation N t ⁻¹' E) =
      (fourierMeasure N).real E :=
    congrArg ENNReal.toReal ((measurePreserving_angularTranslation N t).measure_preimage
      hE.nullMeasurableSet)
  have h₁ := measureReal_inter_add_sdiff (μ := fourierMeasure N) (s := E) hp
  have h₂ := measureReal_inter_add_sdiff (μ := fourierMeasure N)
    (s := angularTranslation N t ⁻¹' E) hE
  rw [inter_comm] at h₂
  unfold angularTranslationLoss
  linarith

/-- The zero shift has no loss, so only the `n` positive shifts contribute. -/
theorem half_measure_le_shiftIntersection_of_loss {N n : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    (hn : 0 < n) (t : AddCircle (1 : ℝ))
    (hsmall : ∀ j : Fin n, angularTranslationLoss E ((j.val + 1) • t) ≤
      (fourierMeasure N).real E / (2 * (n : ℝ))) :
    (fourierMeasure N).real E / 2 ≤
      (fourierMeasure N).real (shiftIntersection E n t) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (∑ j : Fin (n + 1),
      (fourierMeasure N).real (E \ angularTranslation N (j.val • t) ⁻¹' E)) ≤
        (fourierMeasure N).real E / 2 := by
    simp_rw [measure_removed_eq_angularTranslationLoss hE]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_smul, angularTranslationLoss_zero, zero_add, Fin.val_succ]
    calc
      _ ≤ ∑ _j : Fin n, (fourierMeasure N).real E / (2 * (n : ℝ)) :=
        Finset.sum_le_sum fun j _ => hsmall j
      _ = _ := by simp; field_simp
  have h := measureReal_iInter_ge (fourierMeasure N) E
    (fun j : Fin (n + 1) => angularTranslation N (j.val • t) ⁻¹' E)
  change _ ≤ (fourierMeasure N).real (⋂ j : Fin (n + 1),
    angularTranslation N (j.val • t) ⁻¹' E)
  linarith

/-- A substantial angular translation selects a scale with the exact desired
gain and half-measure intersections for all smaller shifts. -/
theorem exists_critical_angular_shift {N n : ℕ}
    {E : Set (SignVector N × AddCircle (1 : ℝ))} (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (hn : 0 < n)
    (hreach : ∃ t : AddCircle (1 : ℝ), (fourierMeasure N).real E / (2 * (n : ℝ)) ≤
      angularTranslationLoss E t) :
    ∃ τ : ℝ, 0 < τ ∧ (n : ℝ) * τ < 1 ∧
      angularTranslationLoss E (((n : ℝ) * τ : ℝ) : AddCircle (1 : ℝ)) =
        (fourierMeasure N).real E / (2 * (n : ℝ)) ∧
      ∀ t : ℝ, 0 < t → t < τ → (fourierMeasure N).real E / 2 ≤
        (fourierMeasure N).real (shiftIntersection E n (t : AddCircle (1 : ℝ))) := by
  obtain ⟨s, hs⟩ := hreach
  let T := AddCircle.equivIco (1 : ℝ) 0 s
  have hT : (T.val : AddCircle (1 : ℝ)) = s := AddCircle.coe_equivIco
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨u, hu, heq, hbefore⟩ := exists_first_angular_loss hE
    (c := (fourierMeasure N).real E / (2 * (n : ℝ)))
    (div_pos hpos (by positivity)) T.property.1 (by rwa [hT])
  refine ⟨u / n, div_pos hu.1 hnr, ?_, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ hnr.ne']
    exact hu.2.trans_lt (by simpa only [zero_add] using T.property.2)
  · rwa [mul_div_cancel₀ _ hnr.ne']
  · intro t ht htτ
    apply half_measure_le_shiftIntersection_of_loss hE hn
    intro j
    have hj : ((j.val + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hnt : (n : ℝ) * t < u := by
      have := (lt_div_iff₀ hnr).mp htτ
      nlinarith
    have harg : ((j.val + 1 : ℕ) : ℝ) * t ∈ Ico (0 : ℝ) u :=
      ⟨by positivity, (mul_le_mul_of_nonneg_right hj ht.le).trans_lt hnt⟩
    simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using (hbefore _ harg).le

/-- Either restricted energy is already large, or the same critical scale
gives a definite measure gain and all coefficient-uniform shift relations. -/
theorem critical_shift_or_restricted_energy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p) :
    let n := shiftOrder ((fourierMeasure N).real E) p
    (∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      (fourierMeasure N).real E / 4 ≤
        ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∨
    (∃ τ : ℝ, 0 < τ ∧ (n : ℝ) * τ < 1 ∧
      angularTranslationLoss E (((n : ℝ) * τ : ℝ) : AddCircle (1 : ℝ)) =
        (fourierMeasure N).real E / (2 * (n : ℝ)) ∧
      ∀ t : ℝ, 0 < t → t < τ → ∀ a : Fin (N + 1) → ℂ,
        ∃ c : Fin (n + 1) → ℂ, (∑ j, ‖c j‖ ^ 2) = 1 ∧
          (∫ z, ‖∑ j, c j * randomFourier a
            (angularTranslation N (j.val • (t : AddCircle (1 : ℝ))) z)‖ ^ 2
              ∂fourierMeasure N) ≤
            (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E) *
              ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) := by
  dsimp only
  rcases restricted_energy_dichotomy_at_shiftOrder E hE hpos p hp with hreach | henergy
  · have hn := two_le_shiftOrder hpos measureReal_le_one p hp
    obtain ⟨τ, hτ, hperiod, hgain, hhalf⟩ := exists_critical_angular_shift hE hpos
      (by omega) hreach
    refine Or.inr ⟨τ, hτ, hperiod, hgain, fun t ht0 htτ a => ?_⟩
    exact exists_small_shift_relation_of_half_measure E hpos p hp
      (t : AddCircle (1 : ℝ)) (hhalf t ht0 htτ) a
  · exact Or.inl henergy

end Erdos522.LogMoments

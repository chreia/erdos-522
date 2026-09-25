/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SmallShifts
import Mathlib.MeasureTheory.Group.Prod

/-!
# Angular sections and averaged translation loss

Averaging the loss under every angular translation gives the Bernoulli variance
of each angular section. Small losses therefore force many sections to be long.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

abbrev AngularCircle := AddCircle (1 : ℝ)
abbrev angularLaw : Measure AngularCircle := AddCircle.haarAddCircle

/-- The angular section at a fixed sign vector. -/
def angularSection {N : ℕ} (E : Set (SignVector N × AngularCircle))
    (ω : SignVector N) : Set AngularCircle := Prod.mk ω ⁻¹' E

/-- The normalized length of an angular section. -/
def angularSectionSize {N : ℕ} (E : Set (SignVector N × AngularCircle))
    (ω : SignVector N) : ℝ := angularLaw.real (angularSection E ω)

lemma measurableSet_angularSection {N : ℕ} {E : Set (SignVector N × AngularCircle)}
    (hE : MeasurableSet E) (ω : SignVector N) : MeasurableSet (angularSection E ω) :=
  measurable_prodMk_left hE

lemma angularSectionSize_nonneg {N : ℕ} (E : Set (SignVector N × AngularCircle))
    (ω : SignVector N) : 0 ≤ angularSectionSize E ω := measureReal_nonneg

lemma angularSectionSize_le_one {N : ℕ} (E : Set (SignVector N × AngularCircle))
    (ω : SignVector N) : angularSectionSize E ω ≤ 1 := measureReal_le_one

/-- The measure added by translating the angular coordinate of an event. -/
def angularTranslationLoss {N : ℕ} (E : Set (SignVector N × AngularCircle))
    (t : AngularCircle) : ℝ :=
  (fourierMeasure N).real ((angularTranslation N t ⁻¹' E) \ E)

private def circleLossIndicator (S : Set AngularCircle) (p : AngularCircle × AngularCircle) : ℝ :=
  {p : AngularCircle × AngularCircle | p.2 + p.1 ∈ S ∧ p.2 ∉ S}.indicator (fun _ => 1) p

private lemma integrable_circleLossIndicator {S : Set AngularCircle} (hS : MeasurableSet S) :
    Integrable (circleLossIndicator S) (angularLaw.prod angularLaw) := by
  have hs : MeasurableSet {p : AngularCircle × AngularCircle | p.2 + p.1 ∈ S ∧ p.2 ∉ S} :=
    (hS.preimage (by fun_prop)).inter (hS.preimage measurable_snd).compl
  exact (integrable_const 1).indicator hs

private lemma integral_circleLossIndicator_left {S : Set AngularCircle} (hS : MeasurableSet S)
    (t : AngularCircle) :
    (∫ θ, circleLossIndicator S (t, θ) ∂angularLaw) =
      angularLaw.real ((fun θ => θ + t) ⁻¹' S \ S) := by
  have heq : (fun θ => circleLossIndicator S (t, θ)) =
      ((fun θ => θ + t) ⁻¹' S \ S).indicator (fun _ => (1 : ℝ)) := by
    ext θ
    rfl
  rw [heq]
  exact integral_indicator_one ((hS.preimage (by fun_prop)).diff hS)

private lemma integral_circleLossIndicator_right {S : Set AngularCircle} (hS : MeasurableSet S)
    (θ : AngularCircle) :
    (∫ t, circleLossIndicator S (t, θ) ∂angularLaw) =
      Sᶜ.indicator (fun _ => angularLaw.real S) θ := by
  by_cases hθ : θ ∈ S
  · have hz : (fun t => circleLossIndicator S (t, θ)) = 0 := by
      ext t
      simp [circleLossIndicator, hθ]
    simp [hz, hθ]
  · have heq : (fun t => circleLossIndicator S (t, θ)) = fun t => S.indicator (fun _ => (1 : ℝ)) (θ + t) := by
      ext t
      by_cases ht : θ + t ∈ S <;> simp [circleLossIndicator, hθ, ht]
    rw [heq, (measurePreserving_add_left angularLaw θ).integral_comp
      (MeasurableEquiv.addLeft θ).measurableEmbedding]
    simp only [Set.indicator_of_mem (show θ ∈ Sᶜ from hθ)]
    exact integral_indicator_one hS

/-- The average angular translation loss of one section is its Bernoulli variance. -/
theorem integral_circle_translation_loss {S : Set AngularCircle} (hS : MeasurableSet S) :
    (∫ t, angularLaw.real ((fun θ => θ + t) ⁻¹' S \ S) ∂angularLaw) =
      angularLaw.real S * (1 - angularLaw.real S) := by
  simp_rw [← integral_circleLossIndicator_left hS]
  rw [integral_integral_swap (f := fun t θ => circleLossIndicator S (t, θ))
    (integrable_circleLossIndicator hS)]
  simp_rw [integral_circleLossIndicator_right hS]
  rw [integral_indicator_const _ hS.compl, smul_eq_mul, measureReal_compl hS, probReal_univ]
  ring

lemma integrable_circle_translation_loss {S : Set AngularCircle} (hS : MeasurableSet S) :
    Integrable (fun t => angularLaw.real ((fun θ => θ + t) ⁻¹' S \ S)) angularLaw := by
  simpa only [integral_circleLossIndicator_left hS] using
    (integrable_circleLossIndicator hS).integral_prod_left

/-- Integrating angular section lengths recovers the event probability. -/
theorem integral_angularSectionSize {N : ℕ} {E : Set (SignVector N × AngularCircle)}
    (hE : MeasurableSet E) :
    (∫ ω, angularSectionSize E ω ∂signMeasure N) = (fourierMeasure N).real E := by
  have h := integral_prod (μ := signMeasure N) (ν := angularLaw)
    (E.indicator (fun _ => (1 : ℝ))) ((integrable_const 1).indicator hE)
  have hmeasure : (∫ q, E.indicator (fun _ => (1 : ℝ)) q
      ∂(signMeasure N).prod angularLaw) = (fourierMeasure N).real E :=
    integral_indicator_one hE
  rw [hmeasure] at h
  symm
  convert h using 1
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  exact (integral_indicator_one (measurableSet_angularSection hE ω)).symm

lemma angularTranslationLoss_eq_section_integral {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E) (t : AngularCircle) :
    angularTranslationLoss E t =
      ∫ ω, angularLaw.real ((fun θ => θ + t) ⁻¹' angularSection E ω \ angularSection E ω)
        ∂signMeasure N := by
  have hm := integral_angularSectionSize ((hE.preimage (angularTranslation N t).measurable).diff hE)
  unfold angularTranslationLoss
  rw [← hm]
  rfl

lemma angularTranslationLoss_eq_sum {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E) (t : AngularCircle) :
    angularTranslationLoss E t =
      ∑ ω : SignVector N, (signMeasure N).real {ω} *
        angularLaw.real ((fun θ => θ + t) ⁻¹' angularSection E ω \ angularSection E ω) := by
  rw [angularTranslationLoss_eq_section_integral hE, integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]

lemma integrable_angularTranslationLoss {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E) :
    Integrable (angularTranslationLoss E) angularLaw := by
  have heq : angularTranslationLoss E = fun t =>
      ∑ ω : SignVector N, (signMeasure N).real {ω} *
        angularLaw.real ((fun θ => θ + t) ⁻¹' angularSection E ω \ angularSection E ω) :=
    funext (angularTranslationLoss_eq_sum hE)
  rw [heq]
  exact integrable_finsetSum _ (fun ω _ =>
    (integrable_circle_translation_loss (measurableSet_angularSection hE ω)).const_mul _)

/-- The averaged translation loss is the mean Bernoulli variance of the angular sections. -/
theorem integral_angularTranslationLoss {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E) :
    (∫ t, angularTranslationLoss E t ∂angularLaw) =
      ∫ ω, angularSectionSize E ω * (1 - angularSectionSize E ω) ∂signMeasure N := by
  simp_rw [angularTranslationLoss_eq_sum hE]
  rw [integral_finsetSum _ (fun ω _ =>
    (integrable_circle_translation_loss (measurableSet_angularSection hE ω)).const_mul _),
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro ω _
  rw [integral_const_mul, integral_circle_translation_loss (measurableSet_angularSection hE ω)]
  rfl

/-- Sign vectors whose angular section occupies more than `1 - 1/n` of the circle. -/
def longSections {N : ℕ} (E : Set (SignVector N × AngularCircle)) (n : ℝ) : Set (SignVector N) :=
  {ω | 1 - 1 / n < angularSectionSize E ω}

/-- Averaged translation loss controls the section mass outside the long sections. -/
theorem integral_short_section_mass_le {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 0 < n) :
    (∫ ω in (longSections E n)ᶜ, angularSectionSize E ω ∂signMeasure N) ≤
      n * ∫ t, angularTranslationLoss E t ∂angularLaw := by
  rw [integral_angularTranslationLoss hE, ← integral_const_mul,
    ← integral_indicator (Set.toFinite ((longSections E n)ᶜ)).measurableSet]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro ω
  have hs0 := angularSectionSize_nonneg E ω
  have hs1 := angularSectionSize_le_one E ω
  by_cases hω : ω ∈ (longSections E n)ᶜ
  · rw [Set.indicator_of_mem hω]
    have hshort : angularSectionSize E ω ≤ 1 - 1 / n := not_lt.mp hω
    have hm : (1 : ℝ) ≤ n * (1 - angularSectionSize E ω) := by
      have h := (div_le_iff₀ hn).mp (show 1 / n ≤ 1 - angularSectionSize E ω by linarith)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hm hs0]
  · rw [Set.indicator_of_notMem hω]
    exact mul_nonneg hn.le (mul_nonneg hs0 (sub_nonneg.mpr hs1))

/-- Few average changes under translations force many long angular sections. -/
theorem measure_longSections_lower_bound {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 0 < n) :
    (fourierMeasure N).real E - n * (∫ t, angularTranslationLoss E t ∂angularLaw) ≤
      (signMeasure N).real (longSections E n) := by
  have hshort := integral_short_section_mass_le hE hn
  have hsplit := integral_add_compl (μ := signMeasure N)
    (s := longSections E n) (f := angularSectionSize E)
    (Set.toFinite _).measurableSet Integrable.of_finite
  rw [integral_angularSectionSize hE] at hsplit
  have hlong : (∫ ω in longSections E n, angularSectionSize E ω ∂signMeasure N) ≤
      (signMeasure N).real (longSections E n) := by
    have h := integral_mono (μ := (signMeasure N).restrict (longSections E n))
      Integrable.of_finite (integrable_const (1 : ℝ)) (angularSectionSize_le_one E)
    simpa using h
  linarith

/-- The quantitative long-section conclusion used when every translation loss is small. -/
theorem half_measure_lt_longSections_of_average_loss {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 0 < n)
    (hloss : (∫ t, angularTranslationLoss E t ∂angularLaw) < (fourierMeasure N).real E / (2 * n)) :
    (fourierMeasure N).real E / 2 < (signMeasure N).real (longSections E n) := by
  have hbound := measure_longSections_lower_bound hE hn
  have h := (lt_div_iff₀ (show 0 < 2 * n by positivity)).mp hloss
  nlinarith

/-- If every angular translation changes less than `δ/(2n)` of the event,
more than `δ/2` of the sign vectors have long sections. -/
theorem half_measure_lt_longSections {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 0 < n)
    (hloss : ∀ t : AngularCircle, angularTranslationLoss E t <
      (fourierMeasure N).real E / (2 * n)) :
    (fourierMeasure N).real E / 2 < (signMeasure N).real (longSections E n) := by
  apply half_measure_lt_longSections_of_average_loss hE hn
  let c := (fourierMeasure N).real E / (2 * n)
  have hint : Integrable (fun t => c - angularTranslationLoss E t) angularLaw :=
    (integrable_const _).sub (integrable_angularTranslationLoss hE)
  have hsupp : Function.support (fun t => c - angularTranslationLoss E t) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact (sub_pos.mpr (hloss t)).ne'
  have hpos : 0 < ∫ t, c - angularTranslationLoss E t ∂angularLaw := by
    apply (integral_pos_iff_support_of_nonneg (fun t => (sub_pos.mpr (hloss t)).le) hint).mpr
    rw [hsupp, measure_univ]
    exact zero_lt_one
  rw [integral_sub (integrable_const _) (integrable_angularTranslationLoss hE),
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hpos
  exact sub_pos.mp hpos

/-- When `n ≥ 2`, long sections occupy at most twice the event measure. -/
theorem measure_longSections_le_twice {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 2 ≤ n) :
    (signMeasure N).real (longSections E n) ≤ 2 * (fourierMeasure N).real E := by
  have hhalf : 1 / n ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hn
  have hpoint (ω : SignVector N) :
      (longSections E n).indicator (fun _ => (1 : ℝ)) ω ≤ 2 * angularSectionSize E ω := by
    by_cases hω : ω ∈ longSections E n
    · rw [Set.indicator_of_mem hω]
      change 1 - 1 / n < angularSectionSize E ω at hω
      linarith
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (by norm_num) (angularSectionSize_nonneg E ω)
  have h := integral_mono (μ := signMeasure N) Integrable.of_finite Integrable.of_finite hpoint
  have heq : (∫ ω, (longSections E n).indicator (fun _ => (1 : ℝ)) ω ∂signMeasure N) =
      (signMeasure N).real (longSections E n) :=
    integral_indicator_one (Set.toFinite _).measurableSet
  rw [heq, integral_const_mul, integral_angularSectionSize hE] at h
  exact h


/-- The part missing from a sign cylinder is the mean complement length of its sections. -/
theorem measure_sign_cylinder_hole {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    (A : Set (SignVector N)) :
    (fourierMeasure N).real ((A ×ˢ Set.univ) \ E) =
      ∫ ω in A, 1 - angularSectionSize E ω ∂signMeasure N := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_angularSectionSize ((hA.prod MeasurableSet.univ).diff hE),
    ← integral_indicator hA]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    have hsection : angularSection ((A ×ˢ Set.univ) \ E) ω =
        (angularSection E ω)ᶜ := by
      ext θ
      simp [angularSection, hω]
    simp only [angularSectionSize, hsection, measureReal_compl
      (measurableSet_angularSection hE ω), probReal_univ]
  · rw [Set.indicator_of_notMem hω]
    have hsection : angularSection ((A ×ˢ Set.univ) \ E) ω = ∅ := by
      ext θ
      simp [angularSection, hω]
    simp [angularSectionSize, hsection]

/-- Each long section omits at most `1/n` of its circle. -/
theorem measure_longSections_hole_le {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    (n : ℝ) :
    (fourierMeasure N).real (((longSections E n) ×ˢ Set.univ) \ E) ≤
      (signMeasure N).real (longSections E n) / n := by
  rw [measure_sign_cylinder_hole hE]
  have hm : MeasurableSet (longSections E n) := (Set.toFinite _).measurableSet
  have h := setIntegral_mono_on (μ := signMeasure N) Integrable.of_finite
    (integrable_const (1 / n)).integrableOn hm (fun ω hω => by
      change 1 - 1 / n < angularSectionSize E ω at hω
      linarith : ∀ ω ∈ longSections E n, 1 - angularSectionSize E ω ≤ 1 / n)
  simpa only [setIntegral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using h

/-- Long sections form a cylinder with at most `2δ/n` of its measure missing. -/
theorem measure_longSections_hole_le_twice {N : ℕ}
    {E : Set (SignVector N × AngularCircle)} (hE : MeasurableSet E)
    {n : ℝ} (hn : 2 ≤ n) :
    (fourierMeasure N).real (((longSections E n) ×ˢ Set.univ) \ E) ≤
      2 * (fourierMeasure N).real E / n := by
  exact (measure_longSections_hole_le hE n).trans
    (div_le_div_of_nonneg_right (measure_longSections_le_twice hE hn) (by linarith))

end Erdos522.LogMoments

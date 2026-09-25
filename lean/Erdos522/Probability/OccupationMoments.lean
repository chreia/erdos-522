/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# First and second moments of angular occupation

An occupation is the fraction of angular parameters for which an event occurs.
Fubini turns its first and second moments into one- and two-point probabilities.
Exceptional angular sets contribute only their normalized measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Erdos522

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- The angular fraction occupied by a measurable random event. -/
def occupation (ν : Measure Θ) (E : Set (Θ × Ω)) (ω : Ω) : ℝ :=
  ν.real ((fun θ => (θ, ω)) ⁻¹' E)

/-- The event that occurs at both members of a pair of angular parameters. -/
def pairedOccupationEvent (E : Set (Θ × Ω)) : Set ((Θ × Θ) × Ω) :=
  {p | (p.1.1, p.2) ∈ E ∧ (p.1.2, p.2) ∈ E}

theorem measurableSet_pairedOccupationEvent {E : Set (Θ × Ω)} (hE : MeasurableSet E) :
    MeasurableSet (pairedOccupationEvent E) :=
  (hE.preimage (by fun_prop)).inter (hE.preimage (by fun_prop))

theorem measurable_occupation (ν : Measure Θ) [SFinite ν]
    {E : Set (Θ × Ω)} (hE : MeasurableSet E) : Measurable (occupation ν E) :=
  (measurable_measure_prodMk_right hE).ennreal_toReal

omit [MeasurableSpace Ω] in
theorem occupation_nonneg (ν : Measure Θ) (E : Set (Θ × Ω)) (ω : Ω) :
    0 ≤ occupation ν E ω := measureReal_nonneg

omit [MeasurableSpace Ω] in
theorem occupation_le_one (ν : Measure Θ) [IsProbabilityMeasure ν]
    (E : Set (Θ × Ω)) (ω : Ω) : occupation ν E ω ≤ 1 := measureReal_le_one

/-- Probability normalization makes every occupation bounded in every finite `Lᵖ` space. -/
theorem memLp_occupation (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E) (p : ℝ≥0∞) :
    MemLp (occupation ν E) p μ := by
  apply MemLp.of_bound (measurable_occupation ν hE).aestronglyMeasurable 1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (occupation_nonneg ν E ω)]
  exact occupation_le_one ν E ω

/-- Fubini identifies the mean occupation with the average one-point event probability. -/
theorem integral_occupation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E) :
    (∫ ω, occupation ν E ω ∂μ) = ∫ θ, μ.real (Prod.mk θ ⁻¹' E) ∂ν := by
  have hl : (∫ θ, μ.real (Prod.mk θ ⁻¹' E) ∂ν) = (ν.prod μ).real E := by
    rw [measureReal_def, Measure.prod_apply hE]
    exact integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)
  have hr : (∫ ω, occupation ν E ω ∂μ) = (ν.prod μ).real E := by
    rw [measureReal_def, Measure.prod_apply_symm hE]
    exact integral_toReal (measurable_measure_prodMk_right hE).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)
  exact hr.trans hl.symm

omit [MeasurableSpace Ω] in
/-- The square of an occupation is the occupation of the paired event. -/
theorem occupation_sq_eq_pair (ν : Measure Θ) [SFinite ν]
    (E : Set (Θ × Ω)) (ω : Ω) :
    occupation ν E ω ^ 2 = occupation (ν.prod ν) (pairedOccupationEvent E) ω := by
  change ν.real ((fun θ => (θ, ω)) ⁻¹' E) ^ 2 =
    (ν.prod ν).real (((fun θ => (θ, ω)) ⁻¹' E) ×ˢ ((fun θ => (θ, ω)) ⁻¹' E))
  rw [measureReal_prod_prod, pow_two]

/-- Fubini identifies the second occupation moment with average paired event probability. -/
theorem integral_sq_occupation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E) :
    (∫ ω, occupation ν E ω ^ 2 ∂μ) =
      ∫ p : Θ × Θ, μ.real {ω | (p.1, ω) ∈ E ∧ (p.2, ω) ∈ E} ∂ν.prod ν := by
  simp_rw [occupation_sq_eq_pair]
  exact integral_occupation μ (ν.prod ν) (measurableSet_pairedOccupationEvent hE)

/-- A bounded probability function accumulates at most the measure of its exceptional set. -/
theorem abs_integral_sub_le_of_exceptional (ν : Measure Θ) [IsProbabilityMeasure ν]
    (f : Θ → ℝ) (hf : Measurable f) (h0 : ∀ θ, 0 ≤ f θ) (h1 : ∀ θ, f θ ≤ 1)
    (p δ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (B : Set Θ) (hB : MeasurableSet B) (hgood : ∀ θ ∉ B, |f θ - p| ≤ δ) :
    |(∫ θ, f θ ∂ν) - p| ≤ δ + ν.real B := by
  have hfint : Integrable f ν := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun θ => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 θ)]; exact h1 θ)
  have hbint : Integrable (fun θ => δ + B.indicator (fun _ => (1 : ℝ)) θ) ν :=
    (integrable_const δ).add ((integrable_const 1).indicator hB)
  have hbound (θ : Θ) : |f θ - p| ≤ δ + B.indicator (fun _ => (1 : ℝ)) θ := by
    by_cases hθ : θ ∈ B
    · rw [Set.indicator_of_mem hθ]
      have ha : |f θ - p| ≤ 1 := abs_le.mpr ⟨by linarith [h0 θ], by linarith [h1 θ]⟩
      linarith
    · rw [Set.indicator_of_notMem hθ, add_zero]
      exact hgood θ hθ
  calc
    _ = |∫ θ, f θ - p ∂ν| := by rw [integral_sub hfint (integrable_const p)]; simp
    _ ≤ ∫ θ, |f θ - p| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ θ, δ + B.indicator (fun _ => (1 : ℝ)) θ ∂ν :=
      integral_mono (hfint.sub (integrable_const p)).abs hbint hbound
    _ = _ := by
      rw [integral_add (integrable_const δ) ((integrable_const 1).indicator hB)]
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      exact integral_indicator_one (μ := ν) hB

/-- A one-point probability estimate controls the mean occupation with its angular failure budget. -/
theorem integral_occupation_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E)
    (p δ η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (B : Set Θ) (hB : MeasurableSet B) (hbad : ν.real B ≤ η)
    (hgood : ∀ θ ∉ B, |μ.real (Prod.mk θ ⁻¹' E) - p| ≤ δ) :
    |(∫ ω, occupation ν E ω ∂μ) - p| ≤ δ + η := by
  rw [integral_occupation μ ν hE]
  exact (abs_integral_sub_le_of_exceptional ν _
    (measurable_measure_prodMk_left hE).ennreal_toReal (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) p δ hp0 hp1 hδ B hB hgood).trans (add_le_add (le_refl δ) hbad)

/-- A paired probability estimate controls the second occupation moment with its angular failure budget. -/
theorem integral_sq_occupation_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E)
    (p δ η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (B : Set (Θ × Θ)) (hB : MeasurableSet B) (hbad : (ν.prod ν).real B ≤ η)
    (hgood : ∀ q ∉ B, |μ.real {ω | (q.1, ω) ∈ E ∧ (q.2, ω) ∈ E} - p ^ 2| ≤ δ) :
    |(∫ ω, occupation ν E ω ^ 2 ∂μ) - p ^ 2| ≤ δ + η := by
  rw [integral_sq_occupation μ ν hE]
  have hp : p ^ 2 ≤ 1 := by nlinarith
  exact (abs_integral_sub_le_of_exceptional (ν.prod ν) _
    (measurable_measure_prodMk_left (measurableSet_pairedOccupationEvent hE)).ennreal_toReal
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (p ^ 2) δ (sq_nonneg p) hp hδ B hB hgood).trans (add_le_add (le_refl δ) hbad)

/-- The mean of an occupation lies in the unit interval. -/
theorem integral_occupation_mem_Icc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E) :
    (∫ ω, occupation ν E ω ∂μ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (occupation_nonneg ν E)
  · have h := integral_mono ((memLp_occupation μ ν hE 1).integrable (by norm_num))
      (integrable_const (1 : ℝ)) (occupation_le_one ν E)
    simpa using h

/-- One- and two-point probability errors give an explicit occupation variance bound. -/
theorem variance_occupation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] {E : Set (Θ × Ω)} (hE : MeasurableSet E)
    (p δ₁ η₁ δ₂ η₂ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (B₁ : Set Θ) (hB₁ : MeasurableSet B₁) (hbad₁ : ν.real B₁ ≤ η₁)
    (B₂ : Set (Θ × Θ)) (hB₂ : MeasurableSet B₂) (hbad₂ : (ν.prod ν).real B₂ ≤ η₂)
    (hgood₁ : ∀ θ ∉ B₁, |μ.real (Prod.mk θ ⁻¹' E) - p| ≤ δ₁)
    (hgood₂ : ∀ q ∉ B₂, |μ.real {ω | (q.1, ω) ∈ E ∧ (q.2, ω) ∈ E} - p ^ 2| ≤ δ₂) :
    variance (occupation ν E) μ ≤ δ₂ + η₂ + 2 * (δ₁ + η₁) := by
  have hfirst := integral_occupation_error_le μ ν hE p δ₁ η₁ hp0 hp1 hδ₁ B₁ hB₁ hbad₁ hgood₁
  have hsecond := integral_sq_occupation_error_le μ ν hE p δ₂ η₂ hp0 hp1 hδ₂ B₂ hB₂ hbad₂ hgood₂
  have hmean := integral_occupation_mem_Icc μ ν hE
  have heta : 0 ≤ η₁ := measureReal_nonneg.trans hbad₁
  let a := ∫ ω, occupation ν E ω ∂μ
  have hdiff : p - a ≤ δ₁ + η₁ := by
    have h := (abs_le.mp hfirst).1
    dsimp [a]
    linarith
  have hsquare : p ^ 2 - a ^ 2 ≤ 2 * (δ₁ + η₁) := by
    calc
      _ = (p - a) * (p + a) := by ring
      _ ≤ (δ₁ + η₁) * (p + a) :=
        mul_le_mul_of_nonneg_right hdiff (add_nonneg hp0 hmean.1)
      _ ≤ (δ₁ + η₁) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hmean.2]) (add_nonneg hδ₁ heta)
      _ = _ := by ring
  rw [variance_eq_sub (memLp_occupation μ ν hE 2)]
  have hsecond' := (abs_le.mp hsecond).2
  change (∫ ω, occupation ν E ω ^ 2 ∂μ) - a ^ 2 ≤ _
  linarith

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Concentration of finite event counts

The variance of a finite count is the sum of covariances over ordered pairs.
A designated set of exceptional pairs can be controlled by a one-event
probability bound, while the remaining covariances use a uniform error bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Erdos522

/-- The real-valued count of the events in a finite indexed family. Repeated
    events remain distinct indices and are counted with their multiplicities. -/
def indicatorCount {Ω ι : Type*} [Fintype ι] (E : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω

theorem measurable_indicatorCount {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) : Measurable (indicatorCount E) :=
  Finset.measurable_sum _ fun i _ => measurable_const.indicator (hE i)

theorem memLp_indicatorCount {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) : MemLp (indicatorCount E) 2 μ :=
  memLp_finsetSum _ fun i _ => (memLp_const (μ := μ) (1 : ℝ)).indicator (hE i)

/-- The expectation of the count is the sum of the event probabilities. -/
theorem integral_indicatorCount {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) :
    (∫ ω, indicatorCount E ω ∂μ) = ∑ i, μ.real (E i) := by
  unfold indicatorCount
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hE i))]
  simp only [integral_indicator_const (1 : ℝ) (hE _), smul_eq_mul, mul_one]

theorem integral_indicatorCount_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) {p : ℝ} (hp : ∀ i, μ.real (E i) ≤ p) :
    (∫ ω, indicatorCount E ω ∂μ) ≤ (Fintype.card ι : ℝ) * p := by
  rw [integral_indicatorCount E hE]
  calc
    _ ≤ ∑ _i : ι, p := Finset.sum_le_sum fun i _ => hp i
    _ = (Fintype.card ι : ℝ) * p := by simp

/-- Covariance of two event indicators, including equal or repeated events. -/
theorem covariance_indicator_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E F : Set Ω}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    covariance (E.indicator (fun _ => (1 : ℝ))) (F.indicator (fun _ => (1 : ℝ))) μ =
      μ.real (E ∩ F) - μ.real E * μ.real F := by
  rw [covariance_eq_sub ((memLp_const (μ := μ) (1 : ℝ)).indicator hE)
    ((memLp_const (μ := μ) (1 : ℝ)).indicator hF)]
  have hmul : E.indicator (fun _ => (1 : ℝ)) * F.indicator (fun _ => (1 : ℝ)) =
      (E ∩ F).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hωE : ω ∈ E <;> by_cases hωF : ω ∈ F <;>
      simp [hωE, hωF]
  rw [hmul, integral_indicator_const (1 : ℝ) (hE.inter hF),
    integral_indicator_const (1 : ℝ) hE, integral_indicator_const (1 : ℝ) hF]
  simp only [smul_eq_mul, mul_one]

/-- The exact count variance is a sum over all ordered pairs, including the
    diagonal. -/
theorem variance_indicatorCount_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) :
    variance (indicatorCount E) μ =
      ∑ i, ∑ j, (μ.real (E i ∩ E j) - μ.real (E i) * μ.real (E j)) := by
  unfold indicatorCount
  rw [variance_fun_sum (fun i => (memLp_const (μ := μ) (1 : ℝ)).indicator (hE i))]
  simp only [covariance_indicator_eq (hE _) (hE _)]

/-- Exceptional ordered pairs cost at most one marginal probability each;
    all other ordered pairs cost the stated covariance error. -/
theorem variance_indicatorCount_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (D : Finset (ι × ι))
    {p ε : ℝ} (_hp0 : 0 ≤ p) (hε : 0 ≤ ε) (hp : ∀ i, μ.real (E i) ≤ p)
    (hcov : ∀ i j, (i, j) ∉ D →
      |μ.real (E i ∩ E j) - μ.real (E i) * μ.real (E j)| ≤ ε) :
    variance (indicatorCount E) μ ≤ (Fintype.card ι : ℝ) ^ 2 * ε + (D.card : ℝ) * p := by
  rw [variance_indicatorCount_eq E hE, ← Fintype.sum_prod_type
    (f := fun ij : ι × ι => μ.real (E ij.1 ∩ E ij.2) - μ.real (E ij.1) * μ.real (E ij.2))]
  have hpair (ij : ι × ι) :
      μ.real (E ij.1 ∩ E ij.2) - μ.real (E ij.1) * μ.real (E ij.2) ≤
        ε + if ij ∈ D then p else 0 := by
    by_cases hij : ij ∈ D
    · rw [ite_eq_left hij]
      have hm : μ.real (E ij.1 ∩ E ij.2) ≤ p :=
        (measureReal_mono Set.inter_subset_left).trans (hp ij.1)
      have hprod : 0 ≤ μ.real (E ij.1) * μ.real (E ij.2) :=
        mul_nonneg measureReal_nonneg measureReal_nonneg
      linarith
    · rw [ite_eq_right hij, add_zero]
      exact (le_abs_self _).trans (hcov ij.1 ij.2 hij)
  calc
    _ ≤ ∑ ij : ι × ι, (ε + if ij ∈ D then p else 0) :=
      Finset.sum_le_sum fun ij _ => hpair ij
    _ = (Fintype.card ι : ℝ) ^ 2 * ε + (D.card : ℝ) * p := by
      rw [Finset.sum_add_distrib]
      simp [pow_two]

/-- A threshold at least twice the expectation gives a one-sided Chebyshev
    bound with the exact constant four. -/
theorem measure_ge_le_four_variance_div_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {Q : ℝ} (hQ : 0 < Q) (hmean : (∫ ω, X ω ∂μ) ≤ Q / 2) :
    μ {ω | Q ≤ X ω} ≤ ENNReal.ofReal (4 * variance X μ / Q ^ 2) := by
  have hsub : {ω | Q ≤ X ω} ⊆ {ω | Q / 2 ≤ |X ω - ∫ x, X x ∂μ|} := by
    intro ω hω
    change Q ≤ X ω at hω
    exact (show Q / 2 ≤ X ω - ∫ x, X x ∂μ by linarith).trans (le_abs_self _)
  apply (measure_mono hsub).trans
  have h := meas_ge_le_variance_div_sq hX (half_pos hQ)
  convert h using 1
  congr 1
  field_simp
  ring

/-- The real-probability form of the one-sided Chebyshev bound. -/
theorem measureReal_ge_le_four_variance_div_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {Q : ℝ} (hQ : 0 < Q) (hmean : (∫ ω, X ω ∂μ) ≤ Q / 2) :
    μ.real {ω | Q ≤ X ω} ≤ 4 * variance X μ / Q ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (measure_ge_le_four_variance_div_sq hX hQ hmean)
  have hnonneg : 0 ≤ 4 * variance X μ / Q ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (variance_nonneg X μ)) (sq_nonneg Q)
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using h

/-- A count tail bound from its marginal and ordered-pair covariance bounds. -/
theorem measureReal_indicatorCount_ge_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (D : Finset (ι × ι))
    {p ε Q : ℝ} (hp0 : 0 ≤ p) (hε : 0 ≤ ε) (hQ : 0 < Q)
    (hp : ∀ i, μ.real (E i) ≤ p)
    (hcov : ∀ i j, (i, j) ∉ D →
      |μ.real (E i ∩ E j) - μ.real (E i) * μ.real (E j)| ≤ ε)
    (hthreshold : (Fintype.card ι : ℝ) * p ≤ Q / 2) :
    μ.real {ω | Q ≤ indicatorCount E ω} ≤
      4 * ((Fintype.card ι : ℝ) ^ 2 * ε + (D.card : ℝ) * p) / Q ^ 2 := by
  apply (measureReal_ge_le_four_variance_div_sq (memLp_indicatorCount E hE) hQ
    ((integral_indicatorCount_le E hE hp).trans hthreshold)).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (variance_indicatorCount_le E hE D hp0 hε hp hcov)
      (by norm_num)) (sq_nonneg Q)

end Erdos522

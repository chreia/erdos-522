/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Norm averages on finite measurable partitions

Averaging the norm of a function over each cell of a finite measurable
partition decreases its squared integral. The same statement holds for any
finite disjoint family of cells, with the averaged function set to zero on
their complement.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Erdos522

/-- The average norm on a measurable cell, using zero for a zero-mass cell. -/
def normCellAverage {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (s : Set Ω) (f : Ω → E) : ℝ :=
  (∫ x in s, ‖f x‖ ∂μ) / μ.real s

/-- The function whose value on each cell is that cell's average norm. -/
def partitionNormAverage {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [Fintype ι] (μ : Measure Ω) (s : ι → Set Ω) (f : Ω → E) (x : Ω) : ℝ :=
  ∑ i, (s i).indicator (fun _ => normCellAverage μ (s i) f) x

theorem normCellAverage_nonneg {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (s : Set Ω) (f : Ω → E) : 0 ≤ normCellAverage μ s f :=
  div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) measureReal_nonneg

theorem partitionNormAverage_nonneg {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) (s : ι → Set Ω) (f : Ω → E)
    (x : Ω) : 0 ≤ partitionNormAverage μ s f x := by
  apply Finset.sum_nonneg
  intro i _
  exact Set.indicator_nonneg (fun _ _ => normCellAverage_nonneg μ (s i) f) x

/-- Cauchy--Schwarz for the integral of a norm on a finite measure space. -/
theorem sq_integral_norm_le_mass_mul_integral_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → E}
    (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hnorm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf.norm
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hnorm
    (memLp_const (μ := μ) (1 : ℝ))
  simp only [norm_norm, norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, ← Real.sqrt_eq_rpow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg (fun x => norm_nonneg (f x))) h 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖)),
    Real.sq_sqrt measureReal_nonneg] at hsq
  nlinarith

/-- Each cell's squared average, multiplied by its mass, is bounded by the
    squared norm integral on that cell. -/
theorem mass_mul_normCellAverage_sq_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → E}
    (hf : MemLp f 2 μ) (s : Set Ω) (hs : 0 < μ.real s) :
    μ.real s * normCellAverage μ s f ^ 2 ≤ ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  have h := sq_integral_norm_le_mass_mul_integral_sq (hf.restrict s)
  simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  have heq : μ.real s * normCellAverage μ s f ^ 2 =
      (∫ x in s, ‖f x‖ ∂μ) ^ 2 / μ.real s := by
    unfold normCellAverage
    field_simp
  rw [heq]
  exact (div_le_iff₀ hs).mpr (by nlinarith)

/-- On any one of a disjoint family of cells, the averaged function is the
    corresponding cell average. -/
theorem partitionNormAverage_eq_of_mem {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) (s : ι → Set Ω) (f : Ω → E)
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) {i : ι} {x : Ω}
    (hx : x ∈ s i) : partitionNormAverage μ s f x = normCellAverage μ (s i) f := by
  unfold partitionNormAverage
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    have hj : x ∉ s j := fun hj => Set.disjoint_left.mp (hdis hji) hj hx
    exact Set.indicator_of_notMem hj _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The squared averaged function is the sum of the squared cell averages
    supported on their disjoint cells. -/
theorem partitionNormAverage_sq_eq_sum {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) (s : ι → Set Ω) (f : Ω → E)
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) (x : Ω) :
    partitionNormAverage μ s f x ^ 2 =
      ∑ i, (s i).indicator (fun _ => normCellAverage μ (s i) f ^ 2) x := by
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i, hi⟩ := hx
    rw [partitionNormAverage_eq_of_mem μ s f hdis hi, Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hi]
    · intro j _ hji
      have hj : x ∉ s j := fun hj => Set.disjoint_left.mp (hdis hji) hj hi
      exact Set.indicator_of_notMem hj _
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · have hout : ∀ i, x ∉ s i := by simpa only [not_exists] using hx
    simp only [partitionNormAverage, Set.indicator_of_notMem (hout _),
      Finset.sum_const_zero, zero_pow (by omega : 2 ≠ 0)]

/-- Finite cell averages form a measurable real function. -/
theorem measurable_partitionNormAverage {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) (s : ι → Set Ω) (f : Ω → E)
    (hs : ∀ i, MeasurableSet (s i)) : Measurable (partitionNormAverage μ s f) := by
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hs i)

/-- The squared cell-average function is integrable on every finite measure
    space. -/
theorem integrable_partitionNormAverage_sq {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : ι → Set Ω) (f : Ω → E) (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Integrable (fun x => partitionNormAverage μ s f x ^ 2) μ := by
  simp only [partitionNormAverage_sq_eq_sum μ s f hdis]
  exact integrable_finsetSum _ fun i _ => (integrable_const _).indicator (hs i)

/-- The integral of the squared cell-average function is the sum of cell
    masses times squared cell averages. -/
theorem integral_partitionNormAverage_sq {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : ι → Set Ω) (f : Ω → E) (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∫ x, partitionNormAverage μ s f x ^ 2 ∂μ) =
      ∑ i, μ.real (s i) * normCellAverage μ (s i) f ^ 2 := by
  simp only [partitionNormAverage_sq_eq_sum μ s f hdis]
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hs i))]
  simp only [integral_indicator_const _ (hs _), smul_eq_mul]

/-- Averaging norms over a finite disjoint measurable family contracts the
    squared integral. A full partition is the special case when the cells cover
    the space. -/
theorem integral_partitionNormAverage_sq_le {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : ι → Set Ω) {f : Ω → E} (hf : MemLp f 2 μ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hpos : ∀ i, 0 < μ.real (s i)) :
    (∫ x, partitionNormAverage μ s f x ^ 2 ∂μ) ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [integral_partitionNormAverage_sq μ s f hs hdis]
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.norm.integrable_sq
  calc
    _ ≤ ∑ i, ∫ x in s i, ‖f x‖ ^ 2 ∂μ := by
      exact Finset.sum_le_sum fun i _ => mass_mul_normCellAverage_sq_le hf (s i) (hpos i)
    _ = ∫ x in ⋃ i, s i, ‖f x‖ ^ 2 ∂μ :=
      (integral_iUnion_fintype hs hdis (fun _ => hf2.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun x => sq_nonneg ‖f x‖) hf2

/-- The contraction stated directly from measurability and integrability of
    the squared norm. -/
theorem integral_partitionNormAverage_sq_le_of_integrable {Ω E ι : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (s : ι → Set Ω) {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hpos : ∀ i, 0 < μ.real (s i)) :
    (∫ x, partitionNormAverage μ s f x ^ 2 ∂μ) ≤ ∫ x, ‖f x‖ ^ 2 ∂μ :=
  integral_partitionNormAverage_sq_le s
    ((memLp_two_iff_integrable_sq_norm hf).mpr hf2) hs hdis hpos

/-- Every finite cell-average function belongs to `L²`. -/
theorem memLp_partitionNormAverage {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : ι → Set Ω) (f : Ω → E) (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) :
    MemLp (partitionNormAverage μ s f) 2 μ :=
  (memLp_two_iff_integrable_sq
    (measurable_partitionNormAverage μ s f hs).aestronglyMeasurable).mpr
      (integrable_partitionNormAverage_sq μ s f hs hdis)

/-- On a product with a finite first space, taking cell averages in the second
    variable preserves joint measurability. -/
theorem measurable_partitionNormAverage_prod {Ω₀ Ω E ι : Type*}
    [MeasurableSpace Ω₀] [Finite Ω₀] [MeasurableSingletonClass Ω₀]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι]
    (ν : Measure Ω) (s : ι → Set Ω) (f : Ω₀ × Ω → E)
    (hs : ∀ i, MeasurableSet (s i)) :
    Measurable (fun q : Ω₀ × Ω => partitionNormAverage ν s (fun x => f (q.1, x)) q.2) := by
  unfold partitionNormAverage
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable (fun ω : Ω₀ => normCellAverage ν (s i) (fun x => f (ω, x))) :=
    measurable_of_finite _
  exact Measurable.ite ((hs i).preimage measurable_snd)
    (hi.comp measurable_fst) measurable_const

/-- The square of the sectionwise cell-average function is jointly integrable
    when the first space and both measures are finite. -/
theorem integrable_partitionNormAverage_prod_sq {Ω₀ Ω E ι : Type*}
    [MeasurableSpace Ω₀] [Finite Ω₀] [MeasurableSingletonClass Ω₀]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι]
    (μ : Measure Ω₀) (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : ι → Set Ω) (f : Ω₀ × Ω → E) (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Integrable (fun q : Ω₀ × Ω =>
      partitionNormAverage ν s (fun x => f (q.1, x)) q.2 ^ 2) (μ.prod ν) := by
  apply (integrable_prod_iff
    ((measurable_partitionNormAverage_prod ν s f hs).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun ω => integrable_partitionNormAverage_sq ν s (fun x => f (ω, x)) hs hdis
  · exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))

set_option maxHeartbeats 500000 in
/-- Averaging only in the second variable contracts the product squared
    integral, while retaining the value of the finite first coordinate. -/
theorem integral_partitionNormAverage_prod_sq_le {Ω₀ Ω E ι : Type*}
    [MeasurableSpace Ω₀] [Finite Ω₀] [MeasurableSingletonClass Ω₀]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι]
    (μ : Measure Ω₀) (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : ι → Set Ω) {f : Ω₀ × Ω → E}
    (hf : ∀ ω, MemLp (fun x => f (ω, x)) 2 ν)
    (hf2 : Integrable (fun q => ‖f q‖ ^ 2) (μ.prod ν))
    (hs : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hpos : ∀ i, 0 < ν.real (s i)) :
    (∫ q, partitionNormAverage ν s (fun x => f (q.1, x)) q.2 ^ 2 ∂μ.prod ν) ≤
      ∫ q, ‖f q‖ ^ 2 ∂μ.prod ν := by
  rw [integral_prod _ (integrable_partitionNormAverage_prod_sq μ ν s f hs hdis),
    integral_prod _ hf2]
  have hleft : Integrable (fun ω : Ω₀ =>
      ∫ x, partitionNormAverage ν s (fun y => f (ω, y)) x ^ 2 ∂ν) μ :=
    integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))
  have hright : Integrable (fun ω : Ω₀ => ∫ x, ‖f (ω, x)‖ ^ 2 ∂ν) μ :=
    integrableOn_univ.mp (IntegrableOn.of_finite (Set.toFinite Set.univ))
  exact integral_mono hleft hright fun ω =>
    integral_partitionNormAverage_sq_le s (hf ω) hs hdis hpos

end Erdos522

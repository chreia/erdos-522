/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.CriticalApproximation
import Erdos522.Analysis.SpreadingPartition
import Erdos522.Analysis.LocalEnergyTransfer

/-!
# Energy propagation through dense angular cells

A restriction estimate for harmonic exponential polynomials on a measurable
part of an interval transfers to the actual finite Fourier polynomial.
Disjoint-cell summation and the real-to-circle change of variables preserve
all normalization factors.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Erdos522

/-- Summing local energy inequalities over a finite disjoint family costs no
factor depending on the number of cells. -/
theorem integral_iUnion_le_of_cell_energy {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (cells : ι → Set Ω)
    (hc : ∀ i, MeasurableSet (cells i))
    (hd : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (E : Set Ω) (hE : MeasurableSet E) (g h : Ω → ℝ)
    (hg : Integrable g μ) (hh : Integrable h μ)
    (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    {A c : ℝ} (hA : 0 ≤ A) (hc0 : 0 ≤ c)
    (hlocal : ∀ i, (∫ x in cells i, g x ∂μ) ≤
      A * ((∫ x in E ∩ cells i, g x ∂μ) + c * ∫ x in cells i, h x ∂μ)) :
    (∫ x in ⋃ i, cells i, g x ∂μ) ≤
      A * ((∫ x in E, g x ∂μ) + c * ∫ x, h x ∂μ) := by
  have hdE : Pairwise (fun i j => Disjoint (E ∩ cells i) (E ∩ cells j)) :=
    fun i j hij => (hd hij).mono inter_subset_right inter_subset_right
  have hsumG : (∑ i, ∫ x in E ∩ cells i, g x ∂μ) ≤ ∫ x in E, g x ∂μ := by
    rw [← integral_iUnion_fintype (fun i => hE.inter (hc i)) hdE
      (fun _ => hg.integrableOn)]
    exact setIntegral_mono_set hg.integrableOn (ae_of_all _ hg0)
      (ae_of_all _ (iUnion_subset fun _ => inter_subset_left))
  have hsumH : (∑ i, ∫ x in cells i, h x ∂μ) ≤ ∫ x, h x ∂μ := by
    rw [← integral_iUnion_fintype hc hd (fun _ => hh.integrableOn)]
    exact setIntegral_le_integral hh (ae_of_all _ hh0)
  rw [integral_iUnion_fintype hc hd (fun _ => hg.integrableOn)]
  calc
    _ ≤ ∑ i, A * ((∫ x in E ∩ cells i, g x ∂μ) + c * ∫ x in cells i, h x ∂μ) :=
      Finset.sum_le_sum fun i _ => hlocal i
    _ = A * ((∑ i, ∫ x in E ∩ cells i, g x ∂μ) +
        c * ∑ i, ∫ x in cells i, h x ∂μ) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hsumG (mul_le_mul_of_nonneg_left hsumH hc0)) hA

/-- Restricting a circle integral to a uniform cell is exactly the ordinary
Lebesgue integral over its half-open real representative. -/
theorem integral_circlePartitionCell_eq_real {q : ℕ} (hq : 0 < q) (i : Fin q)
    (f : AddCircle (1 : ℝ) → ℝ) :
    (∫ θ in circlePartitionCell i, f θ ∂AddCircle.haarAddCircle) =
      ∫ x in unitIntervalCell i, f (x : AddCircle (1 : ℝ)) := by
  rw [← integral_indicator (measurableSet_circlePartitionCell i),
    ← integral_unitInterval_lift_eq_haar]
  have heq : (fun x : ℝ => (circlePartitionCell i).indicator f
      (x : AddCircle (1 : ℝ))) =ᵐ[unitIntervalMeasure]
      (unitIntervalCell i).indicator (fun x : ℝ => f (x : AddCircle (1 : ℝ))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ico] with x hx
    by_cases hi : x ∈ unitIntervalCell i
    · rw [indicator_of_mem ((mem_circlePartitionCell_coe i hx).mpr hi), indicator_of_mem hi]
    · rw [indicator_of_notMem (fun h => hi ((mem_circlePartitionCell_coe i hx).mp h)),
        indicator_of_notMem hi]
  rw [integral_congr_ae heq, integral_indicator (measurableSet_unitIntervalCell i),
    unitIntervalMeasure_restrict_cell hq i]

/-- The dense-cell union inherits any uniform local energy estimate. -/
theorem integral_densePartitionCells_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (cells : ι → Set Ω)
    (hc : ∀ i, MeasurableSet (cells i))
    (hd : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (E : Set Ω) (hE : MeasurableSet E) (g h : Ω → ℝ)
    (hg : Integrable g μ) (hh : Integrable h μ)
    (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    {γ A c : ℝ} (hA : 0 ≤ A) (hc0 : 0 ≤ c)
    (hlocal : ∀ i, γ * μ.real (cells i) ≤ μ.real (E ∩ cells i) →
      (∫ x in cells i, g x ∂μ) ≤
        A * ((∫ x in E ∩ cells i, g x ∂μ) + c * ∫ x in cells i, h x ∂μ)) :
    (∫ x in densePartitionCells μ cells E γ, g x ∂μ) ≤
      A * ((∫ x in E, g x ∂μ) + c * ∫ x, h x ∂μ) := by
  classical
  let selected i := if γ * μ.real (cells i) ≤ μ.real (E ∩ cells i)
    then cells i else ∅
  have hsel (i : ι) : selected i ⊆ cells i := by
    dsimp only [selected]
    split_ifs <;> simp
  apply integral_iUnion_le_of_cell_energy μ selected
    (fun i => by dsimp only [selected]; split_ifs <;> simp_all)
    (fun i j hij => (hd hij).mono (hsel i) (hsel j)) E hE g h hg hh hg0 hh0 hA hc0
  intro i
  dsimp only [selected]
  split_ifs with hden
  · exact hlocal i hden
  · simp

/-- Integration on a product cell with a fixed finite coordinate retains
exactly the probability mass of that coordinate. -/
theorem integral_singleton_prod {Ω Θ : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace Θ]
    (μ : Measure Ω) (ν : Measure Θ) [SFinite μ] [SFinite ν]
    (f : Ω × Θ → ℝ) (hf : Integrable f (μ.prod ν)) (ω : Ω) (J : Set Θ) :
    (∫ z in {ω} ×ˢ J, f z ∂μ.prod ν) = μ.real {ω} * ∫ x in J, f (ω, x) ∂ν := by
  rw [setIntegral_prod f hf.integrableOn, integral_singleton]
  rfl

namespace LogMoments

/-- A real angular partition cell with its sign vector fixed. -/
def productRealPartitionCell {N q : ℕ} (i : SignVector N × Fin q) :
    Set (SignVector N × ℝ) := {i.1} ×ˢ unitIntervalCell i.2

theorem measurableSet_productRealPartitionCell {N q : ℕ} (i : SignVector N × Fin q) :
    MeasurableSet (productRealPartitionCell i) :=
  (measurableSet_singleton i.1).prod (measurableSet_unitIntervalCell i.2)

theorem pairwiseDisjoint_productRealPartitionCell {N q : ℕ} (hq : 0 < q) :
    Pairwise (fun i j : SignVector N × Fin q =>
      Disjoint (productRealPartitionCell i) (productRealPartitionCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hfirst : i.1 = j.1 := hi.1.symm.trans hj.1
  have hsecond : i.2 ≠ j.2 := fun h => hij (Prod.ext hfirst h)
  exact Set.disjoint_left.mp (pairwiseDisjoint_unitIntervalCell hq hsecond) hi.2 hj.2

/-- Real and circle product cells agree on the support of the real lift. -/
theorem productRealPartitionCell_ae_eq_preimage {N q : ℕ} (i : SignVector N × Fin q) :
    productRealPartitionCell i =ᵐ[realFourierMeasure N]
      (realToFourierSpace N) ⁻¹' productCirclePartitionCell i := by
  have hunit : ∀ᵐ z ∂realFourierMeasure N, z.2 ∈ Ico (0 : ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ico.preimage measurable_snd)).mpr
      (ae_of_all _ fun _ => self_mem_ae_restrict measurableSet_Ico)
  filter_upwards [hunit] with z hz
  simp only [productRealPartitionCell, productCirclePartitionCell, mem_prod,
    mem_singleton_iff, mem_preimage, realToFourierSpace]
  exact propext (and_congr_right fun _ => (mem_circlePartitionCell_coe i.2 hz).symm)

/-- The energy on the circle equals its real lift on every measurable set. -/
theorem integral_realFourier_preimage {N : ℕ} (a : Fin (N + 1) → ℂ)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) :
    (∫ z in (realToFourierSpace N) ⁻¹' E, ‖realFourier a z‖ ^ 2 ∂realFourierMeasure N) =
      ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N := by
  rw [← integral_indicator (hE.preimage (measurePreserving_realToFourierSpace N).measurable),
    ← integral_indicator hE]
  convert integral_realToFourierSpace_eq (E.indicator (fun z => ‖randomFourier a z‖ ^ 2))
      (((measurable_randomFourier a).norm.pow_const 2).indicator hE).aestronglyMeasurable using 1
  congr 1

/-- Restricting a real product cell preserves both its mass and its mass in
any lifted measurable set. -/
theorem productRealPartitionCell_measure_eq {N q : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (i : SignVector N × Fin q) :
    (realFourierMeasure N).real (productRealPartitionCell i) =
        (fourierMeasure N).real (productCirclePartitionCell i) ∧
      (realFourierMeasure N).real ((realToFourierSpace N) ⁻¹' E ∩ productRealPartitionCell i) =
        (fourierMeasure N).real (E ∩ productCirclePartitionCell i) := by
  have hcell := productRealPartitionCell_ae_eq_preimage i
  have hp := measurePreserving_realToFourierSpace N
  constructor
  · rw [measureReal_congr hcell]
    exact congrArg ENNReal.toReal (hp.measure_preimage
      (measurableSet_productCirclePartitionCell i).nullMeasurableSet)
  · have hinter : ((realToFourierSpace N) ⁻¹' E ∩ productRealPartitionCell i) =ᵐ[
        realFourierMeasure N] (realToFourierSpace N) ⁻¹' (E ∩ productCirclePartitionCell i) := by
      filter_upwards [hcell] with z hz
      exact congrArg (fun b : Prop => z ∈ (realToFourierSpace N) ⁻¹' E ∧ b) hz
    rw [measureReal_congr hinter]
    exact congrArg ENNReal.toReal (hp.measure_preimage
      (hE.inter (measurableSet_productCirclePartitionCell i)).nullMeasurableSet)

/-- The real dense-cell union is the pullback of the circle dense-cell union,
up to the null set outside the chosen real representatives. -/
theorem dense_realPartitionCells_ae_eq_preimage {N q : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) (γ : ℝ) :
    densePartitionCells (realFourierMeasure N) (productRealPartitionCell (q := q))
        ((realToFourierSpace N) ⁻¹' E) γ =ᵐ[realFourierMeasure N]
      (realToFourierSpace N) ⁻¹' densePartitionCells (fourierMeasure N)
        (productCirclePartitionCell (q := q)) E γ := by
  classical
  filter_upwards [ae_all_iff.mpr (fun i : SignVector N × Fin q =>
    productRealPartitionCell_ae_eq_preimage i)] with z hz
  apply propext
  simp only [densePartitionCells, mem_iUnion, mem_preimage]
  apply exists_congr
  intro i
  rw [(productRealPartitionCell_measure_eq E hE i).1,
    (productRealPartitionCell_measure_eq E hE i).2]
  split_ifs
  · exact iff_of_eq (hz i)
  · rfl

/-- Dense-cell energy is identical in the real lift and on the circle. -/
theorem integral_dense_realPartitionCells_eq_circle {N q : ℕ}
    (a : Fin (N + 1) → ℂ)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E) (γ : ℝ) :
    (∫ z in densePartitionCells (realFourierMeasure N)
        (productRealPartitionCell (q := q)) ((realToFourierSpace N) ⁻¹' E) γ,
        ‖realFourier a z‖ ^ 2 ∂realFourierMeasure N) =
      ∫ z in densePartitionCells (fourierMeasure N)
        (productCirclePartitionCell (q := q)) E γ,
        ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N := by
  rw [setIntegral_congr_set (dense_realPartitionCells_ae_eq_preimage E hE γ)]
  exact integral_realFourier_preimage a _
    (measurableSet_densePartitionCells _ _ _ _ measurableSet_productCirclePartitionCell)

/-- Finite families of harmonic exponential polynomials have integrable
squared norm on the sign-and-unit-interval space. -/
theorem integrable_norm_sq_exponential_family {N : ℕ} {S : Set ℝ}
    (P : SignVector N → ℝ → ℂ) (hP : ∀ ω, P ω ∈ exponentialSpan S) :
    Integrable (fun z : SignVector N × ℝ => ‖P z.1 z.2‖ ^ 2) (realFourierMeasure N) := by
  have hm : Measurable (fun z : SignVector N × ℝ => ‖P z.1 z.2‖ ^ 2) :=
    measurable_from_prod_countable_right fun ω =>
      ((continuous_of_mem_exponentialSpan (hP ω)).norm.pow 2).measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun ω => ?_, Integrable.of_finite⟩
  exact ((continuous_of_mem_exponentialSpan (hP ω)).norm.pow 2).integrableOn_Icc.mono_set
    Ico_subset_Icc_self

/-- A set restricted to a product cell is a product with its angular section. -/
theorem inter_productRealPartitionCell {N q : ℕ} (E : Set (SignVector N × ℝ))
    (i : SignVector N × Fin q) :
    E ∩ productRealPartitionCell i =
      {i.1} ×ˢ ((fun x : ℝ => (i.1, x)) ⁻¹' E ∩ unitIntervalCell i.2) := by
  ext ⟨ω, x⟩
  simp only [productRealPartitionCell, mem_inter_iff, mem_prod, mem_singleton_iff, mem_preimage]
  constructor
  · rintro ⟨hE, hω, hx⟩
    exact ⟨hω, by simpa only [hω] using hE, hx⟩
  · rintro ⟨hω, hE, hx⟩
    exact ⟨by simpa only [hω] using hE, hω, hx⟩

/-- Harmonic restriction on individual real cells transfers the energy of an
actual finite Rademacher Fourier sum to the union of dense circle cells.
The factor six comes from the two quadratic approximation inequalities. -/
theorem dense_fourier_energy_le_of_harmonic_restriction {N q m n : ℕ}
    (hq : 0 < q) (a : Fin (N + 1) → ℂ) (ξ : Fin m → ℝ)
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (Φ : SignVector N × ℝ → ℝ) (hΦ : MemLp Φ 2 (realFourierMeasure N))
    {γ A M : ℝ} (hA : 1 ≤ A)
    (happrox : ∀ i : Fin q, ∃ P : SignVector N → ℝ → ℂ,
      (∀ ω, P ω ∈ exponentialSpan (Set.range ξ)) ∧
      ∀ ω x, x ∈ unitIntervalCell i →
        ‖realFourier a (ω, x) - P ω x‖ ≤ M ^ n * Φ (ω, x))
    (hrestrict : ∀ (i : Fin q) (s : Set ℝ), MeasurableSet s → s ⊆ unitIntervalCell i →
      γ * unitIntervalMeasure.real (unitIntervalCell i) ≤ unitIntervalMeasure.real s →
      ∀ P : ℝ → ℂ, P ∈ exponentialSpan (Set.range ξ) →
        (∫ x in unitIntervalCell i, ‖P x‖ ^ 2 ∂unitIntervalMeasure) ≤
          A * ∫ x in s, ‖P x‖ ^ 2 ∂unitIntervalMeasure) :
    (∫ z in densePartitionCells (fourierMeasure N)
        (productCirclePartitionCell (q := q)) E γ,
        ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ≤
      6 * A * ((∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) +
        M ^ (2 * n) * ∫ z, Φ z ^ 2 ∂realFourierMeasure N) := by
  let Er := (realToFourierSpace N) ⁻¹' E
  have hEr : MeasurableSet Er := hE.preimage (measurePreserving_realToFourierSpace N).measurable
  have hΦsq : Integrable (fun z => Φ z ^ 2) (realFourierMeasure N) :=
    (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).mp hΦ
  have hf := integrable_norm_sq_realFourier a
  rw [← integral_dense_realPartitionCells_eq_circle a E hE γ,
    ← integral_realFourier_preimage a E hE]
  have hpow : (M ^ n) ^ 2 = M ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  rw [← hpow]
  apply integral_densePartitionCells_le (realFourierMeasure N)
    (productRealPartitionCell (q := q)) measurableSet_productRealPartitionCell
    (pairwiseDisjoint_productRealPartitionCell hq) Er hEr
    (fun z => ‖realFourier a z‖ ^ 2) (fun z => Φ z ^ 2) hf hΦsq
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (by linarith) (sq_nonneg _)
  intro i hden
  obtain ⟨P, hP, herr⟩ := happrox i.2
  have hp := integrable_norm_sq_exponential_family P hP
  apply integral_norm_sq_le_of_local_approximation (realFourierMeasure N)
    (Er ∩ productRealPartitionCell i) (productRealPartitionCell i)
    (hEr.inter (measurableSet_productRealPartitionCell i))
    (measurableSet_productRealPartitionCell i) inter_subset_right
    (realFourier a) (fun z => P z.1 z.2) Φ hA hf.integrableOn hp.integrableOn hΦsq.integrableOn
    (fun z hz => herr z.1 z.2 hz.2)
  let s := (fun x : ℝ => (i.1, x)) ⁻¹' Er ∩ unitIntervalCell i.2
  have hs : MeasurableSet s := (hEr.preimage (by fun_prop)).inter
    (measurableSet_unitIntervalCell i.2)
  have hcellmass : (realFourierMeasure N).real (productRealPartitionCell i) =
      (signMeasure N).real {i.1} * unitIntervalMeasure.real (unitIntervalCell i.2) :=
    measureReal_prod_prod _ _
  have hsectionmass : (realFourierMeasure N).real (Er ∩ productRealPartitionCell i) =
      (signMeasure N).real {i.1} * unitIntervalMeasure.real s := by
    rw [inter_productRealPartitionCell]
    exact measureReal_prod_prod _ _
  rw [hcellmass, hsectionmass] at hden
  rw [inter_productRealPartitionCell]
  change (∫ z in {i.1} ×ˢ unitIntervalCell i.2, ‖P z.1 z.2‖ ^ 2
      ∂(signMeasure N).prod unitIntervalMeasure) ≤
    A * ∫ z in {i.1} ×ˢ s, ‖P z.1 z.2‖ ^ 2 ∂(signMeasure N).prod unitIntervalMeasure
  rw [integral_singleton_prod _ _ _ hp, integral_singleton_prod _ _ _ hp]
  by_cases hzero : (signMeasure N).real {i.1} = 0
  · simp [hzero]
  · have hw : 0 < (signMeasure N).real {i.1} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero)
    have hden' : γ * unitIntervalMeasure.real (unitIntervalCell i.2) ≤
        unitIntervalMeasure.real s := by nlinarith [hden]
    have hr := hrestrict i.2 s hs inter_subset_right hden' (P i.1) (hP i.1)
    simpa only [mul_left_comm A] using mul_le_mul_of_nonneg_left hr hw.le

/-- The finite multiplier for one spreading step at order `n` and set mass `δ`.
It includes the harmonic restriction, the partition scale, and the squared
local-approximation constant. -/
def spreadingEnergyConstant (n : ℕ) (δ C : ℝ) : ℝ :=
  1 + 6 * (16 * C * n / δ) ^ (2 * n + 1) *
    (1 + (32 * (n : ℝ) ^ 2 / δ) ^ (2 * n) * restrictedApproximationConstant n δ)

/-- At the critical order, either a set already captures a definite amount of
energy, or it grows by `δ/(4n)` while its energy increases by an explicit
factor. The same enlarged set works for every normalized coefficient vector.
The remaining analytic input is an interval restriction theorem for harmonic
exponential polynomials with at most `n` frequencies. -/
theorem restricted_energy_or_spreading_of_harmonic_restriction {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p)
    {C : ℝ} (hC : 1 ≤ C)
    (hrestrict : ∀ (m : ℕ), m ≤ shiftOrder ((fourierMeasure N).real E) p →
      ∀ (ξ : Fin m → ℝ), Function.Injective ξ → ∀ (q : ℕ), 0 < q →
      ∀ (γ : ℝ), 0 < γ → γ ≤ 1 → ∀ (i : Fin q) (s : Set ℝ),
      MeasurableSet s → s ⊆ unitIntervalCell i →
      γ * unitIntervalMeasure.real (unitIntervalCell i) ≤ unitIntervalMeasure.real s →
      ∀ P : ℝ → ℂ, P ∈ exponentialSpan (Set.range ξ) →
        (∫ x in unitIntervalCell i, ‖P x‖ ^ 2 ∂unitIntervalMeasure) ≤
          (C / γ) ^ (2 * shiftOrder ((fourierMeasure N).real E) p + 1) *
            ∫ x in s, ‖P x‖ ^ 2 ∂unitIntervalMeasure) :
    let δ := (fourierMeasure N).real E
    let n := shiftOrder δ p
    (∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      δ / 4 ≤ ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∨
    (∃ E' : Set (SignVector N × AddCircle (1 : ℝ)),
      MeasurableSet E' ∧ E ⊆ E' ∧ δ + δ / (4 * n) ≤ (fourierMeasure N).real E' ∧
      ∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
        (∫ z in E', ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ≤
          spreadingEnergyConstant n δ C * ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) := by
  let δ := (fourierMeasure N).real E
  let n := shiftOrder δ p
  have hδ1 : δ ≤ 1 := measureReal_le_one
  have hn2 : 2 ≤ n := two_le_shiftOrder hpos hδ1 p hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  rcases critical_approximation_or_restricted_energy E hE hpos p hp with henergy | hcritical
  · exact Or.inl henergy
  obtain ⟨τ, hτ, hnτ, hgain, happ⟩ := hcritical
  let Δ := δ / (2 * (n : ℝ))
  have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * (n : ℝ))).mpr
    linarith
  have hτ1 : τ ≤ 1 := by nlinarith
  obtain ⟨q, M, hq, hM1, hMupper, hscale, hgrowth⟩ :=
    exists_spreading_partition (signMeasure N) E hE (by omega : 1 ≤ n)
      hτ hτ1 hΔ hΔ1 hgain
  let γ := Δ / 8
  let A := (C / γ) ^ (2 * n + 1)
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hγ1 : γ ≤ 1 := by dsimp only [γ]; linarith
  have hA : 1 ≤ A := one_le_pow₀ ((le_div_iff₀ hγ).mpr (by linarith))
  let W := densePartitionCells (fourierMeasure N) (productCirclePartitionCell (q := q)) E γ
  have hW : MeasurableSet W :=
    measurableSet_densePartitionCells _ _ _ _ measurableSet_productCirclePartitionCell
  refine Or.inr ⟨E ∪ (W \ E), hE.union (hW.diff hE), subset_union_left, ?_, ?_⟩
  · rw [measureReal_union disjoint_sdiff_right (hW.diff hE)]
    change δ + δ / (4 * (n : ℝ)) ≤ δ + (fourierMeasure N).real (W \ E)
    have hhalf : Δ / 2 = δ / (4 * (n : ℝ)) := by dsimp only [Δ]; ring
    exact add_le_add (le_refl δ) (hhalf ▸ hgrowth)
  · intro a ha
    obtain ⟨m, ξ, hmn, hξ, happrox⟩ := happ a ha
    obtain ⟨Φ, _hΦ0, hΦ, hΦenergy, hP⟩ := happrox q hq M hM1 hscale
    have htrans := dense_fourier_energy_le_of_harmonic_restriction hq a ξ E hE Φ hΦ hA hP
      (fun i s hs hsub hden P hpP =>
        hrestrict m hmn ξ hξ q hq γ hγ hγ1 i s hs hsub hden P hpP)
    have hAeq : A = (16 * C * n / δ) ^ (2 * n + 1) := by
      change (C / (δ / (2 * (n : ℝ)) / 8)) ^ (2 * n + 1) = _
      congr 1
      field_simp
      ring
    have hMbound : M ≤ 32 * (n : ℝ) ^ 2 / δ := by
      convert hMupper using 1
      dsimp only [Δ]
      field_simp
      ring
    have hR := (restrictedApproximationConstant_pos n hpos).le
    have he0 : 0 ≤ ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N :=
      integral_nonneg fun _ => sq_nonneg _
    have hM0 : 0 ≤ M := by linarith
    have hWenergy : (∫ z in W, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ≤
        (spreadingEnergyConstant n δ C - 1) *
          ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N := by
      calc
        _ ≤ 6 * A * ((∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) +
            M ^ (2 * n) * ∫ z, Φ z ^ 2 ∂realFourierMeasure N) := htrans
        _ ≤ 6 * A * ((∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) +
            (32 * (n : ℝ) ^ 2 / δ) ^ (2 * n) *
              (restrictedApproximationConstant n δ *
                ∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)) := by
          gcongr
        _ = _ := by rw [hAeq, spreadingEnergyConstant]; ring
    have hf := integrable_norm_sq_randomFourier a
    rw [setIntegral_union disjoint_sdiff_right (hW.diff hE) hf.integrableOn hf.integrableOn]
    have hsdiff : (∫ z in W \ E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ≤
        ∫ z in W, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N :=
      setIntegral_mono_set hf.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
        (ae_of_all _ sdiff_subset)
    nlinarith

/-- The real unit-interval law restricts to Lebesgue measure on every
measurable subset of a partition cell. -/
theorem unitIntervalMeasure_restrict_subset_cell {q : ℕ} (hq : 0 < q) (i : Fin q)
    (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ unitIntervalCell i) :
    unitIntervalMeasure.restrict s = volume.restrict s := by
  rw [unitIntervalMeasure, Measure.restrict_restrict hs,
    inter_eq_left.mpr (hsub.trans (unitIntervalCell_subset hq i))]

/-- Ordinary Lebesgue restriction estimates on cells use the identical
normalization under the real Fourier probability law. -/
theorem unitInterval_restriction_of_volume {q : ℕ} (hq : 0 < q) (i : Fin q)
    (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ unitIntervalCell i)
    {γ A : ℝ} (P : ℝ → ℂ)
    (hrestrict : γ * volume.real (unitIntervalCell i) ≤ volume.real s →
      (∫ x in unitIntervalCell i, ‖P x‖ ^ 2) ≤ A * ∫ x in s, ‖P x‖ ^ 2) :
    γ * unitIntervalMeasure.real (unitIntervalCell i) ≤ unitIntervalMeasure.real s →
      (∫ x in unitIntervalCell i, ‖P x‖ ^ 2 ∂unitIntervalMeasure) ≤
        A * ∫ x in s, ‖P x‖ ^ 2 ∂unitIntervalMeasure := by
  have hcell : unitIntervalMeasure.real (unitIntervalCell i) =
      volume.real (unitIntervalCell i) := by
    rw [unitIntervalMeasure, measureReal_restrict_apply' measurableSet_Ico,
      inter_eq_left.mpr (unitIntervalCell_subset hq i)]
  have hset : unitIntervalMeasure.real s = volume.real s := by
    rw [unitIntervalMeasure, measureReal_restrict_apply' measurableSet_Ico,
      inter_eq_left.mpr (hsub.trans (unitIntervalCell_subset hq i))]
  rw [hcell, hset, unitIntervalMeasure_restrict_cell hq i,
    unitIntervalMeasure_restrict_subset_cell hq i s hs hsub]
  exact hrestrict

/-- Every spreading multiplier is at least one for a positive set mass and a
nonnegative harmonic restriction constant. -/
theorem one_le_spreadingEnergyConstant (n : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    1 ≤ spreadingEnergyConstant n δ C := by
  have hR := (restrictedApproximationConstant_pos n hδ).le
  unfold spreadingEnergyConstant
  exact le_add_of_nonneg_right (by positivity)

end LogMoments
end Erdos522

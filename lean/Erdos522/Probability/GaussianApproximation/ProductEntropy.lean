/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.RealEntropy
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Relative entropy of finite Gaussian products

Relative entropy is unchanged by measurable changes of coordinates and is
additive under independent products. Consequently the entropy of diagonal
Gaussian covariance matrices is the sum of the scalar variance remainders.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace Erdos522

/-- Relative entropy is invariant under an invertible measurable change of coordinates. -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- Relative entropy adds for two independent probability distributions. -/
theorem klDiv_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  have h := klDiv_compProd_eq_add μ₁ ν₁ (Kernel.const α μ₂) (Kernel.const α ν₂)
  simp only [Measure.compProd_const] at h
  rw [h]
  congr 1
  rw [← klDiv_map_measurableEquiv _ _ (MeasurableEquiv.prodComm (α := α) (β := β))]
  change klDiv ((μ₁.prod μ₂).map Prod.swap) ((μ₁.prod ν₂).map Prod.swap) = _
  rw [Measure.prod_swap, Measure.prod_swap]
  simpa only [Measure.compProd_const] using
    klDiv_compProd_left μ₂ ν₂ (Kernel.const β μ₁)

/-- The entropy of a finite independent product is the sum of its coordinate entropies. -/
theorem klDiv_pi_fin {α : Type*} [MeasurableSpace α] (n : ℕ)
    (μ ν : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    have h : μ = ν := funext fun i => Fin.elim0 i
    subst ν
    simp
  | succ n ih =>
    rw [← klDiv_map_measurableEquiv _ _ (MeasurableEquiv.piFinSuccAbove (fun _ => α) 0),
      (measurePreserving_piFinSuccAbove μ 0).map_eq,
      (measurePreserving_piFinSuccAbove ν 0).map_eq, klDiv_prod, ih]
    simp [Fin.sum_univ_succ]

/-- Exact relative entropy of centered independent Gaussian coordinates. -/
theorem klDiv_pi_gaussianReal {n : ℕ} (v w : Fin n → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) :
    klDiv (Measure.pi fun i => gaussianReal 0 (v i))
        (Measure.pi fun i => gaussianReal 0 (w i)) =
      ∑ i, ENNReal.ofReal (((v i : ℝ) / w i - 1 - Real.log ((v i : ℝ) / w i)) / 2) := by
  rw [klDiv_pi_fin]
  exact Finset.sum_congr rfl fun i _ => klDiv_gaussianReal (hv i) (hw i)

/-- A finite Gaussian product has quadratic entropy cost in its relative variance errors. -/
theorem klDiv_pi_gaussianReal_le {n : ℕ} (v w : Fin n → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hvw : ∀ i, 1 / 2 ≤ (v i : ℝ) / w i) :
    klDiv (Measure.pi fun i => gaussianReal 0 (v i))
        (Measure.pi fun i => gaussianReal 0 (w i)) ≤
      ENNReal.ofReal (∑ i, ((v i : ℝ) / w i - 1) ^ 2) := by
  rw [klDiv_pi_fin, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact Finset.sum_le_sum fun i _ => klDiv_gaussianReal_le (hv i) (hw i) (hvw i)

end Erdos522

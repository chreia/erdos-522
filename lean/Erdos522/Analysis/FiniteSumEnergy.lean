/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Squared energy of finite sums

Cauchy--Schwarz bounds the squared integral of a finite sum by its cardinality
times the sum of the individual squared integrals.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522

/-- The squared integral of a finite real sum obeys the cardinality bound. -/
theorem integral_sum_sq_le_card_mul_sum_integral_sq {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ x, f i x ^ 2 ∂μ := by
  have hsum : MemLp (fun x => ∑ i ∈ s, f i x) 2 μ :=
    memLp_finsetSum s hf
  have hsum2 : Integrable (fun x => (∑ i ∈ s, f i x) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hsum.aestronglyMeasurable).mp hsum
  have hi (i : ι) (hi : i ∈ s) : Integrable (fun x => f i x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hf i hi).aestronglyMeasurable).mp (hf i hi)
  calc
    _ ≤ ∫ x, (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2 ∂μ :=
      integral_mono hsum2 ((integrable_finsetSum s hi).const_mul _)
        (fun x => sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => f i x))
    _ = _ := by rw [integral_const_mul, integral_finsetSum s hi]

/-- A common squared-energy bound gives the square of the number of terms. -/
theorem integral_sum_sq_le_card_sq {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) {B : ℝ}
    (hB : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ B) :
    (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤ (s.card : ℝ) ^ 2 * B := by
  apply (integral_sum_sq_le_card_mul_sum_integral_sq μ s f hf).trans
  calc
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, B := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

end Erdos522

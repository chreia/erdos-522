/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PartitionAverages
import Erdos522.Analysis.FiniteSumEnergy

/-!
# Squared energy of a partition error majorant

A residual norm and finitely many scaled cell averages form a nonnegative
error function. Its squared integral is bounded by the square of the number
of terms times their common energy bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522

/-- A residual norm plus scaled averages on an angular partition. -/
def partitionError {Ω₀ Ω E ι κ : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [Fintype ι] [Fintype κ] (ν : Measure Ω) (s : κ → Set Ω)
    (f₀ : Ω₀ × Ω → E) (f : ι → Ω₀ × Ω → E) (c : ι → ℝ) (q : Ω₀ × Ω) : ℝ :=
  ‖f₀ q‖ + ∑ i, c i * partitionNormAverage ν s (fun x => f i (q.1, x)) q.2

theorem partitionError_nonneg {Ω₀ Ω E ι κ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] [Fintype κ]
    (ν : Measure Ω) (s : κ → Set Ω) (f₀ : Ω₀ × Ω → E)
    (f : ι → Ω₀ × Ω → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (q : Ω₀ × Ω) :
    0 ≤ partitionError ν s f₀ f c q := by
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hc i) (partitionNormAverage_nonneg ν s _ q.2))

/-- The partition majorant belongs to `L²` whenever its residual does. -/
theorem memLp_partitionError {Ω₀ Ω E ι κ : Type*}
    [MeasurableSpace Ω₀] [Finite Ω₀] [MeasurableSingletonClass Ω₀]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι] [Fintype κ]
    (μ : Measure Ω₀) (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : κ → Set Ω) (f₀ : Ω₀ × Ω → E) (f : ι → Ω₀ × Ω → E) (c : ι → ℝ)
    (hs : ∀ j, MeasurableSet (s j)) (hdis : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hf₀ : MemLp f₀ 2 (μ.prod ν)) :
    MemLp (partitionError ν s f₀ f c) 2 (μ.prod ν) := by
  have hA (i : ι) : MemLp (fun q : Ω₀ × Ω =>
      partitionNormAverage ν s (fun x => f i (q.1, x)) q.2) 2 (μ.prod ν) :=
    (memLp_two_iff_integrable_sq
      (measurable_partitionNormAverage_prod ν s (f i) hs).aestronglyMeasurable).mpr
      (integrable_partitionNormAverage_prod_sq μ ν s (f i) hs hdis)
  exact hf₀.norm.add (memLp_finsetSum Finset.univ (fun i _ => (hA i).const_mul (c i)))

/-- The finite partition error obeys the common squared-energy bound. -/
theorem integral_partitionError_sq_le {Ω₀ Ω E ι κ : Type*}
    [MeasurableSpace Ω₀] [Finite Ω₀] [MeasurableSingletonClass Ω₀]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [Fintype ι] [Fintype κ]
    (μ : Measure Ω₀) (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : κ → Set Ω) (f₀ : Ω₀ × Ω → E) (f : ι → Ω₀ × Ω → E) (c : ι → ℝ)
    (hs : ∀ j, MeasurableSet (s j)) (hdis : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hpos : ∀ j, 0 < ν.real (s j))
    (hf₀ : MemLp f₀ 2 (μ.prod ν))
    (hf : ∀ i ω, MemLp (fun x => f i (ω, x)) 2 ν)
    (hfi : ∀ i, Integrable (fun q => ‖f i q‖ ^ 2) (μ.prod ν))
    {B : ℝ} (h₀ : (∫ q, ‖f₀ q‖ ^ 2 ∂μ.prod ν) ≤ B)
    (hi : ∀ i, c i ^ 2 * (∫ q, ‖f i q‖ ^ 2 ∂μ.prod ν) ≤ B) :
    (∫ q, partitionError ν s f₀ f c q ^ 2 ∂μ.prod ν) ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 * B := by
  let A (i : ι) (q : Ω₀ × Ω) := partitionNormAverage ν s (fun x => f i (q.1, x)) q.2
  have hA (i : ι) : MemLp (A i) 2 (μ.prod ν) :=
    (memLp_two_iff_integrable_sq
      (measurable_partitionNormAverage_prod ν s (f i) hs).aestronglyMeasurable).mpr
      (integrable_partitionNormAverage_prod_sq μ ν s (f i) hs hdis)
  let F : Option ι → Ω₀ × Ω → ℝ := fun i =>
    match i with
    | none => fun q => ‖f₀ q‖
    | some i => fun q => c i * A i q
  have hF (i : Option ι) : MemLp (F i) 2 (μ.prod ν) := by
    cases i with
    | none => exact hf₀.norm
    | some i => exact (hA i).const_mul (c i)
  have hb (i : Option ι) : (∫ q, F i q ^ 2 ∂μ.prod ν) ≤ B := by
    cases i with
    | none => exact h₀
    | some i =>
        change (∫ q, (c i * A i q) ^ 2 ∂μ.prod ν) ≤ B
        simp_rw [mul_pow]
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left
          (integral_partitionNormAverage_prod_sq_le μ ν s (hf i) (hfi i) hs hdis hpos)
            (sq_nonneg (c i))).trans (hi i)
  have h := integral_sum_sq_le_card_sq (μ.prod ν) Finset.univ F (fun i _ => hF i) (fun i _ => hb i)
  simpa only [F, A, Fintype.sum_option, partitionError, Finset.card_univ,
    Fintype.card_option, Nat.cast_add, Nat.cast_one] using h

end Erdos522

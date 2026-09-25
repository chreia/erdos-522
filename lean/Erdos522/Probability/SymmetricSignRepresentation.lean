/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.ConditionalLogarithmicMoments
import Mathlib.MeasureTheory.Group.Measure

/-!
# Independent signs for centrally symmetric coefficient laws

A centrally symmetric complex law is unchanged by multiplication by either
sign. For a product of such laws this remains true coordinate by coordinate,
so adjoining independent Rademacher signs preserves the full coefficient law.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- Each fixed sign preserves a centrally symmetric complex measure. -/
theorem measurePreserving_sign_mul (μ : Measure ℂ) [μ.IsNegInvariant] (b : Bool) :
    MeasurePreserving (fun z : ℂ => LogMoments.sign b * z) μ μ := by
  cases b
  · simpa [LogMoments.sign] using
      (show MeasurePreserving (fun z : ℂ => -z) μ μ from
        ⟨measurable_neg, Measure.map_neg_eq_self μ⟩)
  · simpa [LogMoments.sign] using
      (show MeasurePreserving (fun z : ℂ => z) μ μ from
        ⟨measurable_id, Measure.map_id⟩)

/-- Fixed coordinate signs preserve the independent product of centrally
symmetric complex coefficient laws. -/
theorem measurePreserving_coordinate_signs {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsNegInvariant]
    (b : ι → Bool) :
    MeasurePreserving (fun z : ι → ℂ => fun i => LogMoments.sign (b i) * z i)
      (Measure.pi μ) (Measure.pi μ) := by
  have hm : Measurable (fun z : ι → ℂ => fun i => LogMoments.sign (b i) * z i) := by
    fun_prop
  refine ⟨hm, ?_⟩
  rw [Measure.pi_map_pi (fun i => (measurePreserving_sign_mul (μ i) (b i)).measurable.aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_sign_mul (μ i) (b i)).map_eq

/-- Independent random signs leave the entire product coefficient law
unchanged. The auxiliary signs may follow any probability law. -/
theorem measurePreserving_random_coordinate_signs {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, (μ i).IsNegInvariant]
    (ν : Measure (ι → Bool)) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun q : (ι → Bool) × (ι → ℂ) =>
      fun i => LogMoments.sign (q.1 i) * q.2 i) (ν.prod (Measure.pi μ)) (Measure.pi μ) := by
  have hm : Measurable (fun q : (ι → Bool) × (ι → ℂ) =>
      fun i => LogMoments.sign (q.1 i) * q.2 i) := by
    have hs (i : ι) : Measurable (fun q : (ι → Bool) × (ι → ℂ) => LogMoments.sign (q.1 i)) :=
      (measurable_of_finite (fun b : ι → Bool => LogMoments.sign (b i))).comp measurable_fst
    fun_prop
  have hid : MeasurePreserving (fun b : ι → Bool => b) ν ν := ⟨measurable_id, Measure.map_id⟩
  have hskew := hid.skew_product hm (ae_of_all ν fun b =>
    (measurePreserving_coordinate_signs μ b).map_eq)
  exact measurePreserving_snd.comp hskew

/-- Adjoining independent Rademacher signs and an independent angle gives
the same coefficient-and-angle law as the original symmetric model. -/
theorem measurePreserving_rademacher_amplitudes_and_angle {N : ℕ}
    (μ : Fin (N + 1) → Measure ℂ) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsNegInvariant] :
    MeasurePreserving
      (fun q : ((LogMoments.SignVector N) × (Fin (N + 1) → ℂ)) × AddCircle (1 : ℝ) =>
        ((fun k => LogMoments.sign (q.1.1 k) * q.1.2 k), q.2))
      (((LogMoments.signMeasure N).prod (Measure.pi μ)).prod AddCircle.haarAddCircle)
      ((Measure.pi μ).prod AddCircle.haarAddCircle) := by
  exact (measurePreserving_random_coordinate_signs μ (LogMoments.signMeasure N)).prod
    (show MeasurePreserving (fun θ : AddCircle (1 : ℝ) => θ)
      AddCircle.haarAddCircle AddCircle.haarAddCircle from ⟨measurable_id, Measure.map_id⟩)

end Erdos522

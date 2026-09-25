/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.MeasurableSelection
import Erdos522.Probability.LogMoments.ShiftMultipliers
import Erdos522.Probability.LogMoments.QuantitativeShifts

/-!
# Measurable coefficient choices for small shifts

An arbitrarily small strict energy margin permits measurable normalized
coefficients. This allows the weighted Parseval identity to be integrated
in the shift parameter.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos522.LogMoments

/-- Unit coefficient vectors for a relation of order `n`. -/
abbrev UnitCoefficients (n : ℕ) :=
  {c : Fin (n + 1) → ℂ // ∑ j, ‖c j‖ ^ 2 = 1}

instance (n : ℕ) : Nonempty (UnitCoefficients n) := by
  classical
  refine ⟨⟨Pi.single 0 1, ?_⟩⟩
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The coefficients of small-shift relations can be chosen measurably with any positive margin. -/
theorem exists_measurable_small_shift_coefficients {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (I : Set ℝ) {B η : ℝ} (hη : 0 < η)
    (hsmall : ∀ t : I, ∃ c : Fin (n + 1) → ℂ, (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • (t.val : AddCircle (1 : ℝ))) q)‖ ^ 2
          ∂fourierMeasure N) ≤ B) :
    ∃ c : I → Fin (n + 1) → ℂ, Measurable c ∧ ∀ t : I,
      (∑ j, ‖c t j‖ ^ 2) = 1 ∧
      (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier (c t) (t.val : AddCircle (1 : ℝ)) k.val‖ ^ 2) <
        B + η := by
  let F (t : I) (c : UnitCoefficients n) : ℝ :=
    ∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier c.val (t.val : AddCircle (1 : ℝ)) k.val‖ ^ 2
  have ht : Continuous (fun t : I => (t.val : AddCircle (1 : ℝ))) := by fun_prop
  have hm (c : UnitCoefficients n) : Measurable (fun t : I => F t c) :=
    ((continuous_shift_multiplier_energy (n := n) a).comp
      (ht.prodMk continuous_const)).measurable
  have hc (t : I) : Continuous (F t) := by
    apply continuous_finsetSum
    intro k _
    apply Continuous.const_mul
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp continuous_subtype_val).mul_const _
  have he (t : I) : ∃ c : UnitCoefficients n, F t c < B + η := by
    obtain ⟨c, hc, hb⟩ := hsmall t
    rw [integral_shift_combination_eq_multiplier_energy] at hb
    exact ⟨⟨c, hc⟩, lt_of_le_of_lt hb (by linarith)⟩
  obtain ⟨c, hcm, hcb⟩ := exists_measurable_sublevel_selector F (fun _ => B + η)
    hm measurable_const hc he
  exact ⟨fun t => (c t).val, measurable_subtype_coe.comp hcm, fun t => ⟨(c t).property, hcb t⟩⟩

/-- The coefficient-uniform small-shift estimate admits measurable normalized choices
    on one interval that is independent of the Fourier coefficients. -/
theorem exists_measurable_quantitative_small_shifts {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m)
    {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ a : Fin (N + 1) → ℂ,
      ∃ c : Set.Ioo (0 : ℝ) τ →
        Fin (shiftOrder ((fourierMeasure N).real E) m + 1) → ℂ,
        Measurable c ∧ ∀ t : Set.Ioo (0 : ℝ) τ,
          (∑ j, ‖c t j‖ ^ 2) = 1 ∧
          (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier (c t)
            (t.val : AddCircle (1 : ℝ)) k.val‖ ^ 2) <
            (4 * ((shiftOrder ((fourierMeasure N).real E) m : ℝ) + 1) /
              (fourierMeasure N).real E) *
                (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N) + η := by
  obtain ⟨τ, hτ, hsmall⟩ := exists_quantitative_small_shifts E hE hpos m hm
  refine ⟨τ, hτ, fun a => ?_⟩
  exact exists_measurable_small_shift_coefficients a (Set.Ioo (0 : ℝ) τ) hη
    (fun t => hsmall t.val t.property.1 t.property.2 a)

/-- A measurable unit coefficient relation on a measurable set extends to all real shifts. -/
theorem exists_measurable_unit_extension {n : ℕ} (I : Set ℝ) (hI : MeasurableSet I)
    (c : I → Fin (n + 1) → ℂ) (hc : Measurable c)
    (hnorm : ∀ t, ∑ j, ‖c t j‖ ^ 2 = 1) :
    ∃ d : ℝ → Fin (n + 1) → ℂ, Measurable d ∧
      (∀ t, ∑ j, ‖d t j‖ ^ 2 = 1) ∧ (∀ t : I, d t.val = c t) := by
  let u : I → UnitCoefficients n := fun t => ⟨c t, hnorm t⟩
  have hu : Measurable u := hc.subtype_mk
  obtain ⟨v, hv, heq⟩ := (MeasurableEmbedding.subtype_coe hI).exists_measurable_extend hu
    (fun _ => inferInstance)
  refine ⟨fun t => (v t).val, measurable_subtype_coe.comp hv,
    fun t => (v t).property, ?_⟩
  intro t
  exact congrArg Subtype.val (congrFun heq t)

end Erdos522.LogMoments

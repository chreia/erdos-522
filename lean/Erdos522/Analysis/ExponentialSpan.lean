/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialPrimitives
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finite-frequency exponential spans

The span of real-frequency characters consists of finite exponential
polynomials. A nonresonant integrating factor adds at most its own frequency.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- The complex linear span of characters with frequencies in a prescribed set. -/
def exponentialSpan (S : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ ((fun ξ x => angularCharacter (ξ * x)) '' S)

theorem character_mem_exponentialSpan {S : Set ℝ} {ξ : ℝ} (hξ : ξ ∈ S) :
    (fun x => angularCharacter (ξ * x)) ∈ exponentialSpan S :=
  Submodule.subset_span ⟨ξ, hξ, rfl⟩

/-- Every function in an exponential span is continuous. -/
theorem continuous_of_mem_exponentialSpan {S : Set ℝ} {f : ℝ → ℂ}
    (hf : f ∈ exponentialSpan S) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨ξ, _, rfl⟩ := hf
      exact continuous_angularCharacter_mul ξ
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact continuous_const.smul hf

/-- Enlarging the frequency set enlarges its exponential span. -/
theorem exponentialSpan_mono {S T : Set ℝ} (hST : S ⊆ T) :
    exponentialSpan S ≤ exponentialSpan T :=
  Submodule.span_mono (Set.image_mono hST)

/-- The primitive of a nonresonant character lies in the span of the two frequencies. -/
theorem primitive_character_mem_exponentialSpan (ξ η a : ℝ) (hne : η ≠ ξ) :
    oscillatoryPrimitive ξ a (fun t => angularCharacter (η * t)) ∈
      exponentialSpan {ξ, η} := by
  have hη := character_mem_exponentialSpan (show η ∈ ({ξ, η} : Set ℝ) by simp)
  have hξ := character_mem_exponentialSpan (show ξ ∈ ({ξ, η} : Set ℝ) by simp)
  have hlin := (exponentialSpan {ξ, η}).sub_mem
    ((exponentialSpan {ξ, η}).smul_mem (frequencyMultiplier (η - ξ))⁻¹ hη)
    ((exponentialSpan {ξ, η}).smul_mem
      ((frequencyMultiplier (η - ξ))⁻¹ * angularCharacter (-ξ * a) * angularCharacter (η * a)) hξ)
  convert hlin using 1
  ext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [oscillatoryPrimitive_character ξ η a x hne]
  have hphase : angularCharacter (ξ * (x - a)) =
      angularCharacter (ξ * x) * angularCharacter (-ξ * a) := by
    rw [← angularCharacter_add]
    congr 1
    ring
  rw [hphase, div_eq_mul_inv]
  ring

/-- Integration against a frequency outside the source set adds only that frequency. -/
theorem oscillatoryPrimitive_mem_exponentialSpan {S : Set ℝ} {f : ℝ → ℂ}
    (hf : f ∈ exponentialSpan S) (ξ a : ℝ) (hξ : ξ ∉ S) :
    oscillatoryPrimitive ξ a f ∈ exponentialSpan (insert ξ S) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨η, hη, rfl⟩ := hf
      have hne : η ≠ ξ := fun h => hξ (h ▸ hη)
      exact exponentialSpan_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl <;> simp [hη])
        (primitive_character_mem_exponentialSpan ξ η a hne)
  | zero => simpa only [oscillatoryPrimitive_zero]
      using (exponentialSpan (insert ξ S)).zero_mem
  | add f g hf hg ihf ihg =>
      have hfc := continuous_of_mem_exponentialSpan hf
      have hgc := continuous_of_mem_exponentialSpan hg
      rw [oscillatoryPrimitive_add ξ a hfc hgc]
      exact (exponentialSpan (insert ξ S)).add_mem ihf ihg
  | smul c f _ ih =>
      have heq : oscillatoryPrimitive ξ a (c • f) = c • oscillatoryPrimitive ξ a f := by
        ext x
        exact oscillatoryPrimitive_const_mul ξ a c f x
      rw [heq]
      exact (exponentialSpan (insert ξ S)).smul_mem c ih

end Erdos522

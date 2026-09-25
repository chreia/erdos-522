/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.SpectralIntervalSeparation
import Erdos522.Analysis.AngularSeparation

/-!
# Representatives of phases near short spectral intervals

An arithmetic progression meets a separated union of doubled intervals in at
most one point. Selecting that point when it exists, and otherwise keeping the
original representative, puts every nonzero translate at a definite distance
from the original intervals without changing its angular phase.
-/

noncomputable section

open Set

namespace Erdos522

/-- Moving a representative by an integer multiple of `1/t` preserves its phase. -/
theorem angularCharacter_scaled_add_int_div {t : ℝ} (ht : t ≠ 0) (β : ℝ) (k : ℤ) :
    angularCharacter (t * (β + (k : ℝ) / t)) = angularCharacter (t * β) := by
  rw [show t * (β + (k : ℝ) / t) = t * β + (k : ℝ) by field_simp]
  simpa only [Int.cast_neg, sub_neg_eq_add] using angularCharacter_sub_int (t * β) (-k)

/-- A point outside all doubled intervals is more than the radius away from
    every point in the original intervals. -/
theorem gap_of_not_mem_doubledIntervalUnion {T : Finset ℝ} {r x y : ℝ}
    (hx : x ∈ finiteIntervalUnion T r) (hy : y ∉ finiteIntervalUnion T (2 * r)) :
    r < |x - y| := by
  by_contra h
  have habs : |x - y| ≤ r := le_of_not_gt h
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  apply hy
  refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
  have hdist := abs_le.mp habs
  constructor <;> linarith [hxc.1, hxc.2, hdist.1, hdist.2]

/-- Each phase has a representative whose nonzero translates stay at least the
    interval radius away from every point in the original interval union. -/
theorem exists_phase_representative (T : Finset ℝ) (r t : ℝ) (_hr : 0 ≤ r)
    (ht : 0 < t)
    (hsep : ∀ u ∈ finiteIntervalUnion T (2 * r),
      ∀ v ∈ finiteIntervalUnion T (2 * r), ∀ k : ℤ, k ≠ 0 → u - v ≠ (k : ℝ) / t)
    (β : ℝ) :
    ∃ ξ : ℝ, (∃ k : ℤ, ξ = β + (k : ℝ) / t) ∧
      angularCharacter (t * ξ) = angularCharacter (t * β) ∧
      ∀ x ∈ finiteIntervalUnion T r, ∀ j : ℤ, j ≠ 0 → r ≤ |x - (ξ + (j : ℝ) / t)| := by
  classical
  by_cases hex : ∃ k : ℤ, β + (k : ℝ) / t ∈ finiteIntervalUnion T (2 * r)
  · obtain ⟨k, hk⟩ := hex
    refine ⟨β + (k : ℝ) / t, ⟨k, rfl⟩,
      angularCharacter_scaled_add_int_div ht.ne' β k, ?_⟩
    intro x hx j hj
    exact (progression_gap_of_interval_separation hsep hx hk j hj).le
  · refine ⟨β, ⟨0, by simp⟩, rfl, ?_⟩
    intro x hx j _
    exact (gap_of_not_mem_doubledIntervalUnion hx (fun h => hex ⟨j, h⟩)).le

/-- The separation condition makes any representative inside the doubled
    interval union unique within its reciprocal arithmetic progression. -/
theorem phase_representative_unique_in_intervals {T : Finset ℝ} {r t β : ℝ}
    (hsep : ∀ u ∈ finiteIntervalUnion T (2 * r),
      ∀ v ∈ finiteIntervalUnion T (2 * r), ∀ k : ℤ, k ≠ 0 → u - v ≠ (k : ℝ) / t)
    {k l : ℤ} (hk : β + (k : ℝ) / t ∈ finiteIntervalUnion T (2 * r))
    (hl : β + (l : ℝ) / t ∈ finiteIntervalUnion T (2 * r)) : k = l := by
  by_contra h
  apply hsep _ hk _ hl (k - l) (sub_ne_zero.mpr h)
  rw [Int.cast_sub, sub_div]
  ring

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.AngularSeparation

/-!
# Chord bounds from separation of an arithmetic progression

When all nonzero translates of one representative root stay away from a
frequency, its angular factor controls the clipped distance to that root.
-/

noncomputable section
namespace Erdos522

/-- Avoiding the nonzero translates of a root gives a clipped-distance chord bound. -/
theorem chord_lower_bound_of_progression_separation {x ξ τ t δ : ℝ}
    (hτ : 0 < τ) (ht : τ / 2 ≤ t) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ k : ℤ, k ≠ 0 → δ / τ ≤ |x - (ξ + k / t)|) :
    2 * δ * min 1 (τ * |x - ξ|) ≤ ‖angularCharacter (t * (x - ξ)) - 1‖ := by
  have ht0 : 0 < t := by linarith
  let k : ℤ := round (t * (x - ξ))
  have hdist : min (δ / τ) |x - ξ| ≤ |x - (ξ + k / t)| := by
    by_cases hk : k = 0
    · simpa only [hk, Int.cast_zero, zero_div, add_zero] using min_le_right (δ / τ) |x - ξ|
    · exact (min_le_left _ _).trans (hsep k hk)
  have hscale : (δ / τ) * min 1 (τ * |x - ξ|) ≤ min (δ / τ) |x - ξ| := by
    apply le_min
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (τ * |x - ξ|)) (by positivity : 0 ≤ δ / τ)
    · calc
        _ ≤ (δ / τ) * (τ * |x - ξ|) :=
          mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (τ * |x - ξ|)) (by positivity)
        _ = δ * |x - ξ| := by field_simp
        _ ≤ |x - ξ| := by nlinarith [abs_nonneg (x - ξ)]
  have hround : |t * (x - ξ) - k| = t * |x - (ξ + k / t)| := by
    calc
      _ = |t * (x - (ξ + k / t))| := by
        congr 1
        field_simp
        ring
      _ = _ := by rw [abs_mul, abs_of_pos ht0]
  have hchord := four_mul_abs_sub_round_le_chord (t * (x - ξ))
  change 4 * |t * (x - ξ) - k| ≤ _ at hchord
  rw [hround] at hchord
  have hmin : 0 ≤ min 1 (τ * |x - ξ|) := le_min (by norm_num) (by positivity)
  calc
    _ ≤ 4 * t * ((δ / τ) * min 1 (τ * |x - ξ|)) := by
      have hcoef : 2 * δ ≤ 4 * t * (δ / τ) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hτ).mpr
        nlinarith [mul_le_mul_of_nonneg_right ht hδ]
      nlinarith [mul_le_mul_of_nonneg_right hcoef hmin]
    _ ≤ 4 * t * |x - (ξ + k / t)| :=
      mul_le_mul_of_nonneg_left (hscale.trans hdist) (by positivity)
    _ ≤ _ := by simpa only [mul_assoc] using hchord

end Erdos522

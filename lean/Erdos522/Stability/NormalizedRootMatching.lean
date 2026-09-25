/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.NormalizedIncrement
import Erdos522.Probability.RadialCountInterpolation

/-!
# Normalized errors from root matching

Control at a target radius and the two edges of its matching window converts
an integer matching bound into a centered normalized root-count estimate.
-/

noncomputable section
namespace Erdos522
open Polynomial

/-- A three-radius density estimate and root matching give an explicit normalized
error, including the exact degree-increment correction. -/
theorem normalized_root_count_error_of_matching (P Q : ℂ[X]) {N m : ℕ}
    (hN : 0 < N) {r w c δ T D : ℝ} (hw : 0 ≤ w)
    (hcenter : |(closedZeroCount P r : ℝ) / N - c| ≤ δ)
    (hinner : |(closedZeroCount P (r - w) : ℝ) / N - c| ≤ δ)
    (houter : |(closedZeroCount P (r + w) : ℝ) / N - c| ≤ δ)
    (hmatch : (Nat.dist (closedZeroCount Q r) (closedZeroCount P r) : ℝ) ≤
      (closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) + T + D + m) :
    |(closedZeroCount Q r : ℝ) / (N + m) - c| ≤
      3 * δ + T / N + D / N + (1 + |c|) * m / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : closedZeroCount P (r - w) ≤ closedZeroCount P (r + w) :=
    closedZeroCount_mono P (by linarith)
  have hband : ((closedZeroCount P (r + w) - closedZeroCount P (r - w) : ℕ) : ℝ) / N ≤ 2 * δ := by
    rw [Nat.cast_sub hmono, sub_div]
    linarith [(abs_le.mp hinner).1, (abs_le.mp houter).2]
  have hdist : |(closedZeroCount Q r : ℝ) - closedZeroCount P r| / N ≤
      2 * δ + T / N + D / N + m / N := by
    rw [nat_dist_cast_eq_abs] at hmatch
    have h := div_le_div_of_nonneg_right hmatch hn.le
    simp only [add_div] at h
    linarith
  have hnorm := normalized_error_le_after_increment (X := (closedZeroCount P r : ℝ))
    (Y := (closedZeroCount Q r : ℝ)) (c := c) hn (Nat.cast_nonneg m)
  rw [show (1 + |c|) * (m : ℝ) / N = (m : ℝ) / N + |c| * m / N by ring]
  linarith

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.AnnularRootMatching

/-!
# Transporting radial count comparisons between nearby radii

A root-count comparison valid at every radius also controls nearby target
radii. The displacement is absorbed by a doubled reference band.
-/

noncomputable section
namespace Erdos522

/-- A uniform radial matching estimate transports to a nearby target radius,
with the band enlarged by the target displacement. -/
theorem closedZeroCount_transport_bound (P Q : Polynomial ℂ) {w r s : ℝ} {E : ℕ}
    (hw : 0 ≤ w) (hrs : |s - r| ≤ w)
    (hmatch : Nat.dist (closedZeroCount Q s) (closedZeroCount P s) ≤
      closedZeroCount P (s + w) - closedZeroCount P (s - w) + E) :
    Nat.dist (closedZeroCount Q s) (closedZeroCount P r) ≤
      2 * (closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w)) + E := by
  have hsr := abs_le.mp hrs
  have hlow := closedZeroCount_mono P (show r - 2 * w ≤ s - w by linarith)
  have hhigh := closedZeroCount_mono P (show s + w ≤ r + 2 * w by linarith)
  have hsin := closedZeroCount_mono P (show r - 2 * w ≤ s by linarith)
  have hsout := closedZeroCount_mono P (show s ≤ r + 2 * w by linarith)
  have hrin := closedZeroCount_mono P (show r - 2 * w ≤ r by linarith)
  have hrout := closedZeroCount_mono P (show r ≤ r + 2 * w by linarith)
  have hordered := closedZeroCount_mono P (show s - w ≤ s + w by linarith)
  have hband : closedZeroCount P (s + w) - closedZeroCount P (s - w) ≤
      closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) := by omega
  have hshift : Nat.dist (closedZeroCount P s) (closedZeroCount P r) ≤
      closedZeroCount P (r + 2 * w) - closedZeroCount P (r - 2 * w) := by
    rcases le_total (closedZeroCount P s) (closedZeroCount P r) with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      omega
    · rw [Nat.dist_eq_sub_of_le_right h]
      omega
  have htriangle := Nat.dist.triangle_inequality
    (closedZeroCount Q s) (closedZeroCount P s) (closedZeroCount P r)
  omega

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Normalized error under a degree increment

Centering before changing the denominator isolates the degree correction.
This keeps its exact coefficient in quantitative root-count interpolation.
-/

namespace Erdos522

/-- Changing a positive normalization by a nonnegative increment adds a
centered value error and the exact degree correction. -/
theorem normalized_error_le_after_increment {N m X Y c : ℝ} (hN : 0 < N) (hm : 0 ≤ m) :
    |Y / (N + m) - c| ≤ |X / N - c| + |Y - X| / N + |c| * m / N := by
  have hNm : 0 < N + m := by linarith
  have hnum : |(Y - X) + (X - c * N) - c * m| ≤
      |Y - X| + |X - c * N| + |c| * m := by
    calc
      _ ≤ |(Y - X) + (X - c * N)| + |c * m| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg hm]; exact add_le_add (abs_add_le (Y - X) (X - c * N)) le_rfl
  calc
    _ = |((Y - X) + (X - c * N) - c * m) / (N + m)| := by
      congr 1
      field_simp
      ring
    _ = |(Y - X) + (X - c * N) - c * m| / (N + m) := by rw [abs_div, abs_of_pos hNm]
    _ ≤ (|Y - X| + |X - c * N| + |c| * m) / (N + m) :=
      div_le_div_of_nonneg_right hnum hNm.le
    _ ≤ (|Y - X| + |X - c * N| + |c| * m) / N :=
      div_le_div_of_nonneg_left (by positivity) hN (by linarith)
    _ = _ := by
      have hcenter : |X - c * N| / N = |X / N - c| := by
        calc
          _ = |(X - c * N) / N| := by rw [abs_div, abs_of_pos hN]
          _ = _ := by congr 1; field_simp
      rw [add_div, add_div, hcenter]
      ring

end Erdos522

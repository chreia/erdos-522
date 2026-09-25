/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.JensenSecants

/-!
# Closed-disk counts from four logarithmic errors

Two outer Jensen secants squeeze the root count at every radius between their
inner endpoints. The same additive centering constant cancels from both bounds.
-/

noncomputable section
open Polynomial
namespace Erdos522

/-- Four logarithmic errors give a normalized lower and upper root-count bound. -/
theorem radial_fraction_of_four_logarithmic_errors (P : Polynomial ℂ) (F : ℝ → ℝ)
    {N r₀ r₁ r₂ r₃ r e c : ℝ} (hN : 0 < N)
    (h₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₂ : 0 < r₂) (h₂₃ : r₂ < r₃)
    (hrl : r₁ ≤ r) (hru : r ≤ r₂)
    (he₀ : |logCircleAverage P r₀ - F r₀ - c| ≤ e)
    (he₁ : |logCircleAverage P r₁ - F r₁ - c| ≤ e)
    (he₂ : |logCircleAverage P r₂ - F r₂ - c| ≤ e)
    (he₃ : |logCircleAverage P r₃ - F r₃ - c| ≤ e) :
    (F r₁ - F r₀ - 2 * e) / (N * Real.log (r₁ / r₀)) ≤
        (closedZeroCount P r : ℝ) / N ∧
      (closedZeroCount P r : ℝ) / N ≤ (F r₃ - F r₂ + 2 * e) / (N * Real.log (r₃ / r₂)) := by
  have hd₁ := (radial_zero_count_bound P h₀ h₀₁).2
  have hd₂ := (radial_zero_count_bound P h₂ h₂₃).1
  have hc₁ : (closedZeroCount P r₁ : ℝ) ≤ closedZeroCount P r :=
    Nat.cast_le.mpr (closedZeroCount_mono P hrl)
  have hc₂ : (closedZeroCount P r : ℝ) ≤ closedZeroCount P r₂ :=
    Nat.cast_le.mpr (closedZeroCount_mono P hru)
  have hl₁ : 0 < Real.log (r₁ / r₀) := Real.log_pos ((one_lt_div h₀).mpr h₀₁)
  have hl₂ : 0 < Real.log (r₃ / r₂) := Real.log_pos ((one_lt_div h₂).mpr h₂₃)
  rcases abs_le.mp he₀ with ⟨h₀l, h₀u⟩
  rcases abs_le.mp he₁ with ⟨h₁l, h₁u⟩
  rcases abs_le.mp he₂ with ⟨h₂l, h₂u⟩
  rcases abs_le.mp he₃ with ⟨h₃l, h₃u⟩
  constructor
  · have he : F r₁ - F r₀ - 2 * e ≤ logCircleAverage P r₁ - logCircleAverage P r₀ := by linarith
    have hh := div_le_div_of_nonneg_right
      ((div_le_div_of_nonneg_right he hl₁.le).trans (hd₁.trans hc₁)) hN.le
    simpa only [div_div, mul_comm] using hh
  · have he : logCircleAverage P r₃ - logCircleAverage P r₂ ≤ F r₃ - F r₂ + 2 * e := by linarith
    have hh := div_le_div_of_nonneg_right
      ((hc₂.trans hd₂).trans (div_le_div_of_nonneg_right he hl₂.le)) hN.le
    simpa only [div_div, mul_comm] using hh

end Erdos522

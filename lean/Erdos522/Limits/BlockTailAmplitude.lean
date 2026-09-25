/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.TailSupremum
import Erdos522.Limits.PowerBlocks

/-!
# Growth of block-tail amplitudes

Every eighth-power block has positive length. Its common tail amplitude is
therefore bounded below by a positive constant times the square root of the
logarithmic degree, which eventually exceeds every fixed sublevel threshold.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- Positive block length gives a degree-only lower bound for the amplitude. -/
theorem sqrt_log_le_eighth_power_tailAmplitude (j : ℕ) (K₀ : ℝ) :
    15 * Real.exp (2 * K₀) * Real.sqrt (Real.log (j ^ 8 : ℕ)) ≤
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀ := by
  have hM : (1 : ℝ) ≤ eighthPowerBlockLength j := by
    exact_mod_cast eighthPowerBlockLength_pos j
  have hlog : 0 ≤ Real.log (j ^ 8 : ℕ) := Real.log_natCast_nonneg _
  unfold TailSupremum.tailAmplitude
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  nlinarith

/-- The actual eighth-power block-tail amplitude tends to infinity for every
fixed outer-radius parameter. -/
theorem tendsto_eighth_power_tailAmplitude (K₀ : ℝ) :
    Tendsto (fun j : ℕ =>
      TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀) atTop atTop := by
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hp)
  have hroot := Real.tendsto_sqrt_atTop.comp hlog
  have hscale := hroot.const_mul_atTop (by positivity : (0 : ℝ) < 15 * Real.exp (2 * K₀))
  exact tendsto_atTop_mono (fun j => sqrt_log_le_eighth_power_tailAmplitude j K₀) hscale

/-- Every fixed sublevel threshold is eventually below the original block amplitude. -/
theorem eventually_const_le_eighth_power_tailAmplitude (a₀ K₀ : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      a₀ ≤ TailSupremum.tailAmplitude (j ^ 8) (eighthPowerBlockLength j) K₀ :=
  (tendsto_eighth_power_tailAmplitude K₀).eventually_ge_atTop a₀

end Erdos522

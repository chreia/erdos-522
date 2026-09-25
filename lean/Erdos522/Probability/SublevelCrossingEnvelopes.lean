/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseRadialLimits
import Erdos522.Limits.Diagonalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing envelopes for sublevel crossings

The radial band, annular tail, and derivative-small roots contribute three
errors. Fixed probe widths give convergent finite-degree envelopes; a slow
choice of widths makes the combined error vanish while preserving summable
exceptional probabilities.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace Erdos522

/-- The limiting crossing envelope for reciprocal radial probes and annular
width `K + 1`. -/
def sublevelCrossingLimit (K : ℕ) : ℝ :=
  let δ := reciprocalProbeWidth K
  (kacLogVarianceProfile δ - kacLogVarianceProfile (δ / 2)) / (δ / 2) -
    (kacLogVarianceProfile (-δ / 2) - kacLogVarianceProfile (-δ)) / (δ / 2) +
    2 * Real.log 2 / ((K : ℝ) + 1)

/-- The finite-degree envelope for the fraction of roots in crossing sublevel
components. -/
def sublevelCrossingEnvelope (K N : ℕ) : ℝ :=
  radialUpperSecantEnvelope (reciprocalProbeWidth K) N -
    radialLowerSecantEnvelope (reciprocalProbeWidth K) N +
    2 * Real.log 2 / ((K : ℝ) + 1) +
    |radialVarianceSecantEnvelope ((K : ℝ) + 1) N -
      kacAnnularTailCoefficient ((K : ℝ) + 1)| +
    (N : ℝ) ^ (-(1 / 32 : ℝ))

/-- The annular variance envelope is controlled by its limit and its finite
approximation error. -/
theorem radialVarianceSecantEnvelope_le_tail_error (K N : ℕ) :
    radialVarianceSecantEnvelope ((K : ℝ) + 1) N ≤
      2 * Real.log 2 / ((K : ℝ) + 1) +
        |radialVarianceSecantEnvelope ((K : ℝ) + 1) N -
          kacAnnularTailCoefficient ((K : ℝ) + 1)| := by
  have htail := kacAnnularTailCoefficient_le (by positivity : (0 : ℝ) < K + 1)
  have herror := le_abs_self (radialVarianceSecantEnvelope ((K : ℝ) + 1) N -
    kacAnnularTailCoefficient ((K : ℝ) + 1))
  linarith

/-- The derivative-small count threshold has normalized size `N^(-1/32)`. -/
theorem normalized_small_derivative_threshold (N : ℕ) :
    (N : ℝ) ^ (31 / 32 : ℝ) / N = (N : ℝ) ^ (-(1 / 32 : ℝ)) := by
  by_cases hN : N = 0
  · subst N
    norm_num
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [← Real.rpow_sub_one hNr]
    congr 1
    norm_num

/-- The combined band, annular, and derivative errors lie below the crossing
envelope. -/
theorem radial_errors_le_sublevelCrossingEnvelope (K N : ℕ) :
    radialUpperSecantEnvelope (reciprocalProbeWidth K) N -
        radialLowerSecantEnvelope (reciprocalProbeWidth K) N +
      radialVarianceSecantEnvelope ((K : ℝ) + 1) N +
      (N : ℝ) ^ (31 / 32 : ℝ) / N ≤ sublevelCrossingEnvelope K N := by
  rw [normalized_small_derivative_threshold]
  unfold sublevelCrossingEnvelope
  linarith [radialVarianceSecantEnvelope_le_tail_error K N]

/-- At each fixed width, the finite crossing envelope converges to its profile
secants and explicit annular tail bound. -/
theorem tendsto_sublevelCrossingEnvelope (K : ℕ) :
    Tendsto (sublevelCrossingEnvelope K) atTop (𝓝 (sublevelCrossingLimit K)) := by
  unfold sublevelCrossingEnvelope sublevelCrossingLimit
  have hband := (tendsto_radialUpperSecantEnvelope (reciprocalProbeWidth_pos K)).sub
    (tendsto_radialLowerSecantEnvelope (reciprocalProbeWidth_pos K))
  have hannular := ((tendsto_radialVarianceSecantEnvelope
    (by positivity : (0 : ℝ) < K + 1)).sub_const
      (kacAnnularTailCoefficient ((K : ℝ) + 1))).abs
  have hpower := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [sub_self, abs_zero, add_zero, Function.comp_def] using
    ((hband.add_const (2 * Real.log 2 / ((K : ℝ) + 1))).add hannular).add hpower

/-- Shrinking reciprocal probes and increasing annular widths make the
limiting envelope vanish. -/
theorem tendsto_sublevelCrossingLimit :
    Tendsto sublevelCrossingLimit atTop (𝓝 0) := by
  unfold sublevelCrossingLimit
  have htail := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * Real.log 2)
  have hband := tendsto_reciprocal_upper_profile_secant.sub
    tendsto_reciprocal_lower_profile_secant
  simpa only [sub_self, mul_zero, zero_add, mul_one_div]
    using hband.add htail

/-- A deterministic choice of probe widths gives a vanishing crossing envelope
and retains a finite sum of exceptional probabilities. -/
theorem exists_summable_sublevel_crossing_diagonal {p : ℕ → ℕ → ℝ≥0∞}
    (hp : ∀ K, (∑' j, p K j) ≠ ∞) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      Tendsto (fun j => sublevelCrossingEnvelope (s j) (j ^ 8)) atTop (𝓝 0) ∧
      (∑' j, p (s j) j) ≠ ∞ := by
  let b (K j : ℕ) := sublevelCrossingEnvelope K (j ^ 8) - sublevelCrossingLimit K
  have hb (K : ℕ) : Tendsto (b K) atTop (𝓝 0) := by
    have h := ((tendsto_sublevelCrossingEnvelope K).comp
      (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))).sub_const
        (sublevelCrossingLimit K)
    simpa only [b, Function.comp_def, sub_self] using h
  obtain ⟨s, hs, herror, hprob⟩ := exists_diagonal_of_summable_bounds
    tendsto_sublevelCrossingLimit hb hp
  refine ⟨s, hs, ?_, hprob⟩
  apply herror.congr
  intro j
  dsimp [b]
  ring

end Erdos522

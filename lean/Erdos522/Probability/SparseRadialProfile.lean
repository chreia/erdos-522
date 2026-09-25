/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ScaledRadialProbes
import Erdos522.Probability.RademacherStrongLaw

/-!
# The sparse radial profile

Every deterministic radius with scaled displacement tending to `x` has the
same sparse root fraction limit. In particular, the result applies to the
center and both sides of the moving matching window.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522
open LogMoments

theorem tendsto_shifted_lower_profile_secant (x : ℝ) :
    Tendsto (fun m : ℕ =>
      (kacLogVarianceProfile (x - 1 / ((m : ℝ) + 1)) -
        kacLogVarianceProfile (x - 2 * (1 / ((m : ℝ) + 1)))) / (1 / ((m : ℝ) + 1)))
      atTop (𝓝 (kacRadialProfile x)) := by
  have ht := tendsto_two_scale_secant (differentiableAt_kacLogVarianceProfile x).hasDerivAt
    (by norm_num : (-1 : ℝ) ≠ 0)
  apply ht.congr
  intro m
  rw [show (-1 : ℝ) / ((m : ℝ) + 1) = -(1 / ((m : ℝ) + 1)) by ring,
    mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, div_neg]
  ring

theorem tendsto_shifted_upper_profile_secant (x : ℝ) :
    Tendsto (fun m : ℕ =>
      (kacLogVarianceProfile (x + 2 * (1 / ((m : ℝ) + 1))) -
        kacLogVarianceProfile (x + 1 / ((m : ℝ) + 1))) / (1 / ((m : ℝ) + 1)))
      atTop (𝓝 (kacRadialProfile x)) :=
  tendsto_two_scale_secant (differentiableAt_kacLogVarianceProfile x).hasDerivAt (by norm_num : (1 : ℝ) ≠ 0)

theorem eventually_between_scaled_radial_probes {r : ℕ → ℝ} {x : ℝ}
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x))
    {h : ℝ} (hh : 0 < h) :
    ∀ᶠ N : ℕ in atTop, 1 + (x - h) / N ≤ r N ∧ r N ≤ 1 + (x + h) / N := by
  filter_upwards [eventually_ge_atTop 1,
    hr.eventually_const_lt (show x - h < x by linarith),
    hr.eventually_lt_const (show x < x + h by linarith)] with N hN hlo hup
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : (x - h) / N < r N - 1 := (div_lt_iff₀ hn).mpr (by nlinarith)
  have hu : r N - 1 < (x + h) / N := (lt_div_iff₀ hn).mpr (by nlinarith)
  constructor <;> linarith

/-- The sparse radial profile holds at every deterministic asymptotic scaled radius. -/
theorem ae_sparse_radial_profile_of_scaled_radius_limit {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (r : ℕ → ℝ) (x : ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8) (r (j ^ 8)))
        atTop (𝓝 (kacRadialProfile x)) := by
  let w : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hw (m : ℕ) : 0 < w m := by dsimp [w]; positivity
  have hlog : ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, ∀ i : Fin 4,
      |logCircleAverage (polynomialPrefix (fun k => sign (ω k)) (fun _ => 1) (j ^ 8))
          (scaledRadialProbes x (w m) (j ^ 8) i) -
        Real.log (radialSigma (j ^ 8) (scaledRadialProbes x (w m) (j ^ 8) i)) -
          circularLogMean| ≤ logarithmicTolerance (j ^ 8) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_eventually_sparse_radial_logarithmic_bound hC hR (|x| + 2 * w m)
      (by positivity) (scaledRadialProbes x (w m))
      (Filter.Eventually.of_forall fun N i => scaledRadialProbes_mem_annulus x (hw m).le N i) 8 (by norm_num)
  filter_upwards [hlog] with ω hω
  have hp := tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num)
  apply tendsto_of_countable_envelopes _
    (fun m j => scaledLowerSecantEnvelope x (w m) (j ^ 8))
    (fun m j => scaledUpperSecantEnvelope x (w m) (j ^ 8)) _ _ (kacRadialProfile x)
    (fun m => (tendsto_scaledLowerSecantEnvelope x (hw m)).comp hp)
    (fun m => (tendsto_scaledUpperSecantEnvelope x (hw m)).comp hp)
    (tendsto_shifted_lower_profile_secant x) (tendsto_shifted_upper_profile_secant x)
  intro m
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  filter_upwards [hω m, hp.eventually (eventually_between_scaled_radial_probes hr (hw m)),
    ht.eventually_gt_atTop (|x| + 2 * w m)] with j hj hrad hN
  exact radial_fraction_between_scaled_secants
    (rademacherPolynomial (j ^ 8) (rademacherPrefix (j ^ 8) ω)) (j ^ 8) x (hw m) hN hrad.1 hrad.2
    (by simpa only [rademacherPrefix_polynomial] using hj)

/-- Thin power perturbations preserve the prescribed scaled radial coordinate. -/
theorem tendsto_scaled_moving_radius (x s : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((1 + x / N + s * (N : ℝ) ^ (-1 - κ)) - 1))
      atTop (𝓝 x) := by
  have ht := (tendsto_const_nhds (x := x)).add (tendsto_scaled_power_radius s hκ)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-- Sparse profile convergence at the center and either boundary of a matching window. -/
theorem ae_sparse_moving_radius_profile {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) (x s : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (j ^ 8)
        (1 + x / (j ^ 8 : ℕ) + s * ((j ^ 8 : ℕ) : ℝ) ^ (-1 - κ)))
        atTop (𝓝 (kacRadialProfile x)) :=
  ae_sparse_radial_profile_of_scaled_radius_limit hC hR
    (fun N => 1 + x / N + s * (N : ℝ) ^ (-1 - κ)) x (tendsto_scaled_moving_radius x s hκ)

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.RadialSecantApproximation
import Erdos522.Probability.LogarithmicPowerConcentration
import Erdos522.Probability.SparseRadialProfile

/-!
# Sparse radial profiles for every degree exponent greater than two

A countable family of shrinking coordinate probes converts the adjustable
logarithmic concentration estimate into convergence at every deterministic
scaled radius. Each probe uses its own finite concentration constant.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- Jensen secants recover the sparse radial profile at every admissible
clipping exponent. -/
theorem ae_admissible_sparse_radial_profile {q t : ℝ}
    (hq : 2 < q) (ht : 0 < t) (hs : 1 < q * (1 / 2 - 4 * t))
    (r : ℕ → ℝ) (x : ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (realPowerDegree q j) (r (realPowerDegree q j)))
        atTop (𝓝 (kacRadialProfile x)) := by
  let w : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hw (m : ℕ) : 0 < w m := by dsimp [w]; positivity
  have hprobes (m : ℕ) := exists_ae_real_power_logarithmic_power_bound hq ht hs
    (|x| + 2 * w m) (by positivity) (scaledRadialProbes x (w m))
    (Filter.Eventually.of_forall fun N i => scaledRadialProbes_mem_annulus x (hw m).le N i)
  choose H _hH hlog using hprobes
  let e : ℕ → ℕ → ℝ := fun m => logarithmicPowerTolerance t
    (fourierLogarithmicConstant harmonicRestrictionConstant) (H m)
  have he (m : ℕ) : Tendsto (e m) atTop (𝓝 0) := tendsto_logarithmicPowerTolerance ht _ _
  filter_upwards [ae_all_iff.mpr hlog] with ω hω
  have hp := tendsto_realPowerDegree (show 0 < q by linarith)
  apply tendsto_of_countable_envelopes _
    (fun m j => approximateLowerRadialSecant (e m) x (w m) (realPowerDegree q j))
    (fun m j => approximateUpperRadialSecant (e m) x (w m) (realPowerDegree q j)) _ _
    (kacRadialProfile x)
    (fun m => (tendsto_approximateLowerRadialSecant (he m) x (hw m)).comp hp)
    (fun m => (tendsto_approximateUpperRadialSecant (he m) x (hw m)).comp hp)
    (tendsto_shifted_lower_profile_secant x) (tendsto_shifted_upper_profile_secant x)
  intro m
  have hdegree := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hp
  filter_upwards [hω m, hp.eventually (eventually_between_scaled_radial_probes hr (hw m)),
    hdegree.eventually_gt_atTop (|x| + 2 * w m)] with j hj hrad hN
  exact radial_fraction_between_approximate_secants
    (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
      (realPowerDegree q j) (e m) x (hw m) hN hrad.1 hrad.2 hj

/-- Every rounded real-power schedule with `q > 2` has the sparse radial profile. -/
theorem ae_real_power_radial_profile {q : ℝ} (hq : 2 < q) (r : ℕ → ℝ) (x : ℝ)
    (hr : Tendsto (fun N : ℕ => (N : ℝ) * (r N - 1)) atTop (𝓝 x)) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      Tendsto (fun j : ℕ => rademacherRadialFraction ω (realPowerDegree q j) (r (realPowerDegree q j)))
        atTop (𝓝 (kacRadialProfile x)) := by
  have h := admissible_sparse_degree_scales hq
  exact ae_admissible_sparse_radial_profile hq h.logarithmic_pos h.occupation_summability r x hr

end Erdos522

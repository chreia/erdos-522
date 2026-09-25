/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.SublevelComponentCounts
import Erdos522.Probability.SublevelCrossingFailures
import Erdos522.Probability.SublevelCrossingEnvelopes
import Erdos522.Limits.RootLocalizationScales

/-!
# Finite bounds for sublevel components crossing a nearby circle

Curvature control localizes regular annular roots. Jensen secants control the
resulting radial band and the roots outside the annulus, while the annular
derivative estimate controls all remaining multiplicities.
-/

noncomputable section
open Set
namespace Erdos522
open LogMoments

/-- Four logarithmic probes bound the multiplicity-counted band between the
two middle probe radii. -/
theorem radial_band_fraction_le_variance_secants (P : Polynomial ℂ) (N : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hsize : 2 * δ < N)
    (hlog : ∀ i : Fin 4,
      |logCircleAverage P (radialSecantRadii δ N i) -
        Real.log (radialSigma N (radialSecantRadii δ N i)) - circularLogMean| ≤
          logarithmicTolerance N) :
    ((closedZeroCount P (1 + δ / (2 * N)) -
      closedZeroCount P (1 - δ / (2 * N)) : ℕ) : ℝ) / N ≤
        radialUpperSecantEnvelope δ N - radialLowerSecantEnvelope δ N := by
  have hn : (0 : ℝ) < N := by linarith
  have hw : 0 < δ / (2 * N) := by positivity
  have hl : radialSecantRadii δ N 1 = 1 - δ / (2 * N) := by
    simp [radialSecantRadii]
    ring
  have hu : radialSecantRadii δ N 2 = 1 + δ / (2 * N) := by
    simp [radialSecantRadii]
    ring
  have hprobes : radialSecantRadii δ N 1 ≤ radialSecantRadii δ N 2 := by
    rw [hl, hu]
    linarith
  have hinner := (radial_fraction_between_variance_secants P N hδ hsize
    le_rfl hprobes hlog).1
  have houter := (radial_fraction_between_variance_secants P N hδ hsize
    hprobes le_rfl hlog).2
  rw [hl] at hinner
  rw [hu] at houter
  have hmono := closedZeroCount_mono P (by linarith :
    1 - δ / (2 * N) ≤ 1 + δ / (2 * N))
  rw [Nat.cast_sub hmono, sub_div]
  exact sub_le_sub houter hinner

/-- Outside the combined logarithmic, curvature, and derivative exceptions,
the fraction of roots in crossing sublevel components lies below the finite
deterministic envelope. -/
theorem sublevel_crossing_fraction_le_envelope (K N : ℕ) (v : SignVector N)
    {a r : ℝ} (hN : 0 < N)
    (houterSize : 2 * ((K : ℝ) + 1) < N)
    (hinnerSize : 2 * reciprocalProbeWidth K < N)
    (ha : 0 < a) (hd : 0 < regularDerivativeThreshold N)
    (hbudget : 4 * DerivativeSupremum.secondDerivativeEnvelope N ((K : ℝ) + 1) * a ≤
      regularDerivativeThreshold N ^ 2)
    (hradius : 2 * a / regularDerivativeThreshold N ≤ 1 / N)
    (hwindow : 2 * a / regularDerivativeThreshold N + |r - 1| <
      reciprocalProbeWidth K / (2 * N))
    (hgood : v ∉ sublevelCrossingFailure K N) :
    (sublevelComponentZeroCount (rademacherPolynomial N v) a r : ℝ) / N ≤
      sublevelCrossingEnvelope K N := by
  let P := rademacherPolynomial N v
  let A := {z : ℂ | |‖z‖ - 1| ≤ ((K : ℝ) + 1) / N}
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [sublevelCrossingFailure, Set.mem_union, not_or] at hgood
  obtain ⟨⟨⟨houter, hinner⟩, hcurvature⟩, hbad⟩ := hgood
  have houterLog (i : Fin 4) :
      |logCircleAverage P (radialSecantRadii ((K : ℝ) + 1) N i) -
        Real.log (radialSigma N (radialSecantRadii ((K : ℝ) + 1) N i)) - circularLogMean| ≤
          logarithmicTolerance N :=
    le_of_not_gt (fun hlarge => houter ⟨i, hlarge⟩)
  have hinnerLog (i : Fin 4) :
      |logCircleAverage P (radialSecantRadii (reciprocalProbeWidth K) N i) -
        Real.log (radialSigma N (radialSecantRadii (reciprocalProbeWidth K) N i)) - circularLogMean| ≤
          logarithmicTolerance N :=
    le_of_not_gt (fun hlarge => hinner ⟨i, hlarge⟩)
  have hdegree : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · unfold P rademacherPolynomial
      rw [signedPolynomial_eq_ofFn]
      exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
    · change (signedPolynomial (fun _ : Fin (N + 1) => (1 : ℂ)) v).coeff
        (⟨N, by omega⟩ : Fin (N + 1)).val ≠ 0
      rw [coeff_signedPolynomial]
      simpa only [mul_one] using LogMoments.sign_ne_zero (v ⟨N, by omega⟩)
  have hmass := radial_mass_le_variance_secant_envelope P N hdegree
    (by positivity : (0 : ℝ) < K + 1) houterSize houterLog
  have hband := radial_band_fraction_le_variance_secants P N
    (reciprocalProbeWidth_pos K) hinnerSize hinnerLog
  have hderivative :
      (annularSmallDerivativeZeroCount P N ((K : ℝ) + 1)
        ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (31 / 32 : ℝ) :=
    le_of_not_gt hbad
  have hcount := sublevelComponentZeroCount_le_closed_threshold P A ha hd hbudget hwindow
    (by
      intro α _ hα _ z hz
      change |‖α‖ - 1| ≤ ((K : ℝ) + 1) / N at hα
      have hαnorm := (abs_le.mp hα).2
      have hdist : ‖z - α‖ ≤ 2 * a / regularDerivativeThreshold N := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
      have hnorm := norm_sub_norm_le z α
      have hzbound : ‖z‖ ≤ 1 + (((K : ℝ) + 1) + 1) / N := by
        rw [add_div]
        linarith
      exact le_of_not_gt (fun hlarge => hcurvature ⟨z, hzbound, hlarge⟩))
  have hcountReal := (Nat.cast_le (α := ℝ)).mpr hcount
  have hnormalized := div_le_div_of_nonneg_right hcountReal hn.le
  have hderivativeNormalized := div_le_div_of_nonneg_right hderivative hn.le
  dsimp only [A, regularDerivativeThreshold, annularSmallDerivativeZeroCount]
    at hnormalized hderivativeNormalized
  simp only [Nat.cast_add, Set.mem_ofPred_eq] at hnormalized
  rw [add_div, add_div] at hnormalized
  change (sublevelComponentZeroCount P a r : ℝ) / N ≤ _
  apply le_trans _ (radial_errors_le_sublevelCrossingEnvelope K N)
  linarith

end Erdos522

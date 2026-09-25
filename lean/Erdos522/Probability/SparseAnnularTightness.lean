/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SparseRadialMass
import Erdos522.Analysis.KacVarianceProfile

/-!
# Annular tightness of sparse Rademacher zero measures

The geometric variance profile turns the finite Jensen envelope into the
explicit tail coefficient `2 log 2 / K`. A countable intersection over integer
widths then gives tightness on the radial scale `1/N`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Erdos522
open LogMoments

/-- The exact finite variance envelope converges to the four secants of the Kac profile. -/
theorem tendsto_radialVarianceSecantEnvelope {K : ℝ} (hK : 0 < K) :
    Tendsto (radialVarianceSecantEnvelope K) atTop (𝓝 (kacAnnularTailCoefficient K)) := by
  unfold radialVarianceSecantEnvelope
  have hin := ((tendsto_log_radialSigma_sub (-K) (-K / 2)).add
    (tendsto_logarithmicTolerance.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (-K) (-K / 2)) (by linarith : -K / 2 - -K ≠ 0)
  have hout := ((tendsto_log_radialSigma_sub (K / 2) K).sub
    (tendsto_logarithmicTolerance.const_mul 2)).div
      (tendsto_degree_mul_log_radius_ratio (K / 2) K) (by linarith : K - K / 2 ≠ 0)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hin |>.sub hout
  simpa [kacAnnularTailCoefficient, radialSecantRadii,
    show -K / 2 - -K = K / 2 by ring, show K - K / 2 = K / 2 by ring] using ht

/-- Sparse annular tails have the explicit `2 log 2 / K` bound, simultaneously
at every positive integer annular width. -/
theorem ae_sparse_annular_tail_bound_of_harmonic_restriction {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω (K + 1) j ≤
        2 * Real.log 2 / ((K : ℝ) + 1) + ε := by
  filter_upwards [ae_forall_sparse_annular_variance_bound hC hR] with ω hω
  intro K ε hε
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hlim := (tendsto_radialVarianceSecantEnvelope hK).comp
    (tendsto_pow_atTop (α := ℕ) (n := 8) (by norm_num))
  have hcoef := kacAnnularTailCoefficient_le hK
  filter_upwards [hω K, hlim.eventually_lt_const (show kacAnnularTailCoefficient ((K : ℝ) + 1) <
    2 * Real.log 2 / ((K : ℝ) + 1) + ε by linarith)] with j hj hbound
  exact hj.trans hbound.le

/-- The actual sparse root measures are almost surely tight at radial scale `1/N`. -/
theorem ae_sparse_annular_tightness_of_harmonic_restriction {C : ℝ}
    (hC : 1 ≤ C) (hR : HarmonicL2Restriction C) :
    ∀ᵐ ω ∂rademacherSequenceMeasure,
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ᶠ j : ℕ in atTop, sparseAnnularTailFraction ω K j ≤ ε :=
  ae_annular_tightness_of_tail_bounds (ae_sparse_annular_tail_bound_of_harmonic_restriction hC hR)

end Erdos522

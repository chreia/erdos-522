/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularJets
import Erdos522.Probability.GaussianApproximation.JetSmallBall

/-!
# Joint small values of a Steinhaus jet

The covariance lower bound gives the product of the squared complex value
and derivative thresholds, with the explicit Gaussian approximation error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal RealInnerProductSpace
namespace Erdos522

/-- The circular value-derivative small-ball bound holds at every angle. -/
theorem exists_annular_circular_jet_small_ball_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (z : ℂ) (_ : ‖z‖ = 1) (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v),
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
        (circularJet N r z)).real (jetSmallBallSet u v) ≤
      u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 32) ^ 2) +
        circularJetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, happrox⟩ := exists_gaussian_approximation_circular_jet_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r hK hNK hrl hru z hz u v hu hv
  let S := circularCovarianceMatrix (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)
  let c : ℝ≥0 := ⟨Real.exp (-4 * K) / 32, by positivity⟩
  have hc : c ≠ 0 := ne_of_gt (show 0 < c from by change 0 < Real.exp (-4 * K) / 32; positivity)
  have hgram := circular_jet_gram_lower N hN K r hK hNK hrl z hz
  have hS : S.PosDef := circularCovarianceMatrix_posDef _ _ _ (by positivity) hgram
  have hlower (x : EuclideanSpace ℝ (Fin 4)) :
      (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [show S = covarianceMatrix ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
      (circularJet N r z)) from rfl, dotProduct_covarianceMatrix_mulVec]
    exact annular_circular_jet_nondegeneracy N hN K r hK hNK hrl z hz x
  have hg := gaussian_jetSmallBallSet_le S hS.posSemidef c hc hlower u v hu hv
  have hb := (le_abs_self _).trans (happrox N hN K r hK hNK hrl hru z hz
    (jetSmallBallSet u v) (measurableSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u v))
  change (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
    u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 32) ^ 2) at hg
  change ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
      (circularJet N r z)).real (jetSmallBallSet u v) -
    (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
      circularJetGaussianErrorConstant C K / Real.sqrt N at hb
  linarith

end Erdos522

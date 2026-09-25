/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianJets

/-!
# Gaussian polynomial small-ball and separation estimates

The exact Gaussian jet law gives the product scale `u²v²` directly. At two
separated annular points, the covariance comparison controls dependence for
all measurable jet events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped NNReal RealInnerProductSpace
namespace Erdos522

@[fun_prop]
theorem measurable_normalizedGaussianPolynomialJet (N : ℕ) (r : ℝ) (z : ℂ) :
    Measurable (fun g => normalizedPolynomialJet (gaussianPolynomial N g) N (r * z)) := by
  simp_rw [← gaussianVectorSum_realJetCoefficient]
  exact measurable_gaussianVectorSum _

@[fun_prop]
theorem measurable_normalizedGaussianPolynomialJetPair (N : ℕ) (r s : ℝ) (z w : ℂ) :
    Measurable (fun g => normalizedPolynomialJetPair (gaussianPolynomial N g) N (r * z) (s * w)) := by
  simp_rw [← gaussianVectorSum_realPairedJetCoefficient]
  exact measurable_gaussianVectorSum _

/-- Membership records the exact square-root and radial-derivative normalizations. -/
theorem mem_jetSmallBallSet_gaussian (N : ℕ) (hN : 0 < N) (w : ℂ)
    (g : Fin (N + 1) → ℝ) (u v : ℝ) :
    normalizedPolynomialJet (gaussianPolynomial N g) N w ∈ jetSmallBallSet u v ↔
      ‖(gaussianPolynomial N g).eval w‖ ≤ u * Real.sqrt N ∧
      ‖w * (gaussianPolynomial N g).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  simp only [jetSmallBallSet, Set.mem_preimage, jetComplexCoordinates_normalizedPolynomialJet,
    Set.mem_prod, Metric.mem_closedBall, dist_zero_right, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos (mul_pos hn hs),
    div_le_iff₀ hs, div_le_iff₀ (mul_pos hn hs)]

/-- Annular Gaussian jets have the product small-ball scale, without an additive error. -/
theorem gaussian_annular_polynomial_small_ball (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (gaussianCoefficientMeasure (N + 1)).real {g |
      ‖(gaussianPolynomial N g).eval (r * Complex.exp (Complex.I * θ))‖ ≤ u * Real.sqrt N ∧
      ‖(r * Complex.exp (Complex.I * θ)) *
        (gaussianPolynomial N g).derivative.eval (r * Complex.exp (Complex.I * θ))‖ ≤
        v * ((N : ℝ) * Real.sqrt N)} ≤
      u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) := by
  let z := Complex.exp (Complex.I * θ)
  let S := signCovarianceMatrix (realJetCoefficient N r z)
  let c : ℝ≥0 := ⟨Real.exp (-4 * K) / 80, by positivity⟩
  have hc : c ≠ 0 := ne_of_gt (show 0 < c from by
    change 0 < Real.exp (-4 * K) / 80
    positivity)
  have hS : S.PosDef := realJetCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hangle
  have hlower (x : EuclideanSpace ℝ (Fin 4)) : (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [quadratic_signCovarianceMatrix_jet N hN]
    exact real_annular_jet_nondegeneracy N hN K r θ hK hNK hrl hru hdegree hangle x
  have hb := gaussian_jetSmallBallSet_le S hS.posSemidef c hc hlower u v hu hv
  rw [← map_normalizedGaussianPolynomialJet N r z, measureReal_def,
    Measure.map_apply (measurable_normalizedGaussianPolynomialJet N r z)
      (measurableSet_jetSmallBallSet u v)] at hb
  have he : (fun g => normalizedPolynomialJet (gaussianPolynomial N g) N (r * z)) ⁻¹'
      jetSmallBallSet u v = {g |
        ‖(gaussianPolynomial N g).eval (r * z)‖ ≤ u * Real.sqrt N ∧
        ‖(r * z) * (gaussianPolynomial N g).derivative.eval (r * z)‖ ≤
          v * ((N : ℝ) * Real.sqrt N)} := by
    ext g
    exact mem_jetSmallBallSet_gaussian N hN (r * z) g u v
  rw [he] at hb
  exact hb

/-- The two blocks of the paired jet are its individual jets. -/
theorem normalizedPolynomialJetPair_split (P : Polynomial ℂ) (N : ℕ) (z w : ℂ) :
    EuclideanSpace.finAddEquivProd (n := 4) (m := 4) (normalizedPolynomialJetPair P N z w) =
      (normalizedPolynomialJet P N z, normalizedPolynomialJet P N w) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

/-- Separated Gaussian polynomial jets approximately factor for all measurable events. -/
theorem gaussian_annular_jet_factorization (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 4))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(gaussianCoefficientMeasure (N + 1)).real {g |
        normalizedPolynomialJet (gaussianPolynomial N g) N (r * Complex.exp (Complex.I * θ)) ∈ A ∧
        normalizedPolynomialJet (gaussianPolynomial N g) N (s * Complex.exp (Complex.I * φ)) ∈ B} -
      (gaussianCoefficientMeasure (N + 1)).real {g |
        normalizedPolynomialJet (gaussianPolynomial N g) N (r * Complex.exp (Complex.I * θ)) ∈ A} *
      (gaussianCoefficientMeasure (N + 1)).real {g |
        normalizedPolynomialJet (gaussianPolynomial N g) N (s * Complex.exp (Complex.I * φ)) ∈ B}| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  have hb := gaussian_pairedJet_measureReal_prod_le N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum A B hA hB
  rw [← map_normalizedGaussianPolynomialJetPair, ← map_normalizedGaussianPolynomialJet,
    ← map_normalizedGaussianPolynomialJet] at hb
  have hAB : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) :=
    (hA.prod hB).preimage (by fun_prop)
  simp only [measureReal_def, Measure.map_apply (measurable_normalizedGaussianPolynomialJet N r _ ) hA,
    Measure.map_apply (measurable_normalizedGaussianPolynomialJet N s _) hB,
    Measure.map_apply (measurable_normalizedGaussianPolynomialJetPair N r s _ _)
      hAB] at hb
  have he : (fun g => normalizedPolynomialJetPair (gaussianPolynomial N g) N
        (r * Complex.exp (Complex.I * θ)) (s * Complex.exp (Complex.I * φ))) ⁻¹'
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) =
      {g | normalizedPolynomialJet (gaussianPolynomial N g) N (r * Complex.exp (Complex.I * θ)) ∈ A ∧
        normalizedPolynomialJet (gaussianPolynomial N g) N (s * Complex.exp (Complex.I * φ)) ∈ B} := by
    ext g
    simp only [Set.mem_preimage, normalizedPolynomialJetPair_split, Set.mem_prod, Set.mem_ofPred_eq]
  rw [he] at hb
  exact hb

end Erdos522

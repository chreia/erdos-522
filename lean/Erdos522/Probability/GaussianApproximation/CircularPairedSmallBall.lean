/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularCovarianceComparison
import Erdos522.Probability.SteinhausPolynomialJets

/-!
# Two-point probability estimates for circular jets

The joint and marginal Gaussian approximations, together with covariance
comparison, control the dependence of separated jets from one Steinhaus
polynomial. The angular exceptional sets and radial normalizations agree
with the annular mesh estimates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- Approximate factorization for arbitrary measurable convex events in two
separated normalized Steinhaus jets. -/
theorem exists_annular_circular_jet_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
      (A B : Set (EuclideanSpace ℝ (Fin 4)))
      (_ : MeasurableSet A) (_ : MeasurableSet B)
      (_ : Convexity.IsConvexSet ℝ A) (_ : Convexity.IsConvexSet ℝ B),
      |((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularPairedJet N r s
          (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real
        ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
        ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularJet N r
          (Complex.exp (Complex.I * θ)))).real A *
        ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularJet N s
          (Complex.exp (Complex.I * φ)))).real B| ≤
        (2 * circularJetGaussianErrorConstant C K + circularPairedJetGaussianErrorConstant C K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_circular_jet_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_gaussian_approximation_circular_paired_jet_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  let E := (EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)
  have hE : MeasurableSet E := (hA.prod hB).preimage (by fun_prop)
  have hcE : Convexity.IsConvexSet ℝ E := isConvexSet_pair_preimage A B hcA hcB
  have hmono₁ : circularJetGaussianErrorConstant C₁ K ≤ circularJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold circularJetGaussianErrorConstant
    gcongr
    linarith
  have hmono₂ : circularPairedJetGaussianErrorConstant C₂ K ≤ circularPairedJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold circularPairedJetGaussianErrorConstant
    gcongr
    linarith
  have hb₁ := (h₁ N hN K r hK hNK hrl hru (Complex.exp (Complex.I * θ))
    (Complex.norm_exp_I_mul_ofReal θ) A hA hcA).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hb₂ := (h₁ N hN K s hK hNK hsl hsu (Complex.exp (Complex.I * φ))
    (Complex.norm_exp_I_mul_ofReal φ) B hB hcB).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hpair := (h₂ N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree
    hθ hφ hdifference hsum E hE hcE).trans
    (div_le_div_of_nonneg_right hmono₂ (Real.sqrt_nonneg N))
  let p₁ := ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
    (circularJet N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
    (circularJet N s (Complex.exp (Complex.I * φ)))).real B
  let g₁ := (multivariateGaussian 0 (circularCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ))))).real A
  let g₂ := (multivariateGaussian 0 (circularCovarianceMatrix (realJetCoefficient N s (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ))))).real B
  let p := ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularPairedJet N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real E
  let g := (multivariateGaussian 0 (circularCovarianceMatrix (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real E
  have hp₂ : p₂ ≤ 1 := measureReal_le_one
  have hg₁ : g₁ ≤ 1 := measureReal_le_one
  have hm := abs_mul_sub_mul_le_of_unitInterval g₁ g₂ p₁ p₂
    measureReal_nonneg hg₁ measureReal_nonneg hp₂
  have hb₁' : |g₁ - p₁| ≤ circularJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    change |p₁ - g₁| ≤ _ at hb₁
    rwa [abs_sub_comm] at hb₁
  have hb₂' : |g₂ - p₂| ≤ circularJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    change |p₂ - g₂| ≤ _ at hb₂
    rwa [abs_sub_comm] at hb₂
  have hg : |g - g₁ * g₂| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N :=
    gaussian_circularPairedJet_measureReal_prod_le N hN K r s θ φ hK hNK hrl hru hsl hsu
      hdegree hθ hφ hdifference hsum A B hA hB
  change |p - g| ≤ _ at hpair
  change |p - p₁ * p₂| ≤ _
  calc
    _ ≤ |p - g| + |g - g₁ * g₂| + |g₁ * g₂ - p₁ * p₂| := by
      calc
        _ ≤ |p - g| + |g - p₁ * p₂| := abs_sub_le _ _ _
        _ ≤ _ := by linarith [abs_sub_le g (g₁ * g₂) (p₁ * p₂)]
    _ ≤ circularPairedJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
        (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
        (circularJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
          circularJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) :=
      add_le_add (add_le_add hpair hg) (hm.trans (add_le_add hb₁' hb₂'))
    _ = _ := by ring


/-- Splitting a paired circular jet recovers both jets of the same polynomial. -/
theorem finAddEquivProd_circularPairedJet (N : ℕ) (r s : ℝ) (z w : ℂ)
    (a : Fin (N + 1) → ℂ) :
    EuclideanSpace.finAddEquivProd (n := 4) (m := 4) (circularPairedJet N r s z w a) =
      (circularJet N r z a, circularJet N s w a) := by
  rw [circularPairedJet_eq_normalizedPolynomialJetPair,
    circularJet_eq_normalizedPolynomialJet, circularJet_eq_normalizedPolynomialJet]
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

/-- Simultaneous closed thresholds for the value and radial derivative. -/
def circularPolynomialJetSmallBallEvent (N : ℕ) (w : ℂ) (u v : ℝ) :
    Set (Fin (N + 1) → ℂ) :=
  {a | ‖(Polynomial.ofFn (N + 1) a).eval w‖ ≤ u * Real.sqrt N ∧
    ‖w * (Polynomial.ofFn (N + 1) a).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N)}

theorem mem_jetSmallBallSet_circular (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (a : Fin (N + 1) → ℂ) (u v : ℝ) :
    circularJet N r z a ∈ jetSmallBallSet u v ↔
      a ∈ circularPolynomialJetSmallBallEvent N (r * z) u v := by
  rw [circularJet_eq_normalizedPolynomialJet, normalizedPolynomialJet_mem_jetSmallBallSet _ N hN]
  rfl

/-- The one-point jet law measures precisely the polynomial small-ball event. -/
theorem circularJet_measureReal_smallBall (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ) (u v : ℝ) :
    ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularJet N r z)).real (jetSmallBallSet u v) =
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (circularPolynomialJetSmallBallEvent N (r * z) u v) := by
  rw [measureReal_def, Measure.map_apply (measurable_circularJet N r z) (measurableSet_jetSmallBallSet u v)]
  congr 2
  ext ω
  exact mem_jetSmallBallSet_circular N hN r z ω u v

/-- The paired jet rectangle measures the intersection of the actual polynomial events. -/
theorem circularPairedJet_measureReal_smallBall (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (u v u' v' : ℝ) :
    ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularPairedJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) =
      (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real (circularPolynomialJetSmallBallEvent N (r * z) u v ∩
        circularPolynomialJetSmallBallEvent N (s * w) u' v') := by
  have hE : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
      (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) :=
    ((measurableSet_jetSmallBallSet u v).prod (measurableSet_jetSmallBallSet u' v')).preimage
      (by fun_prop)
  rw [measureReal_def, Measure.map_apply (measurable_circularPairedJet N r s z w) hE]
  congr 2
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, finAddEquivProd_circularPairedJet,
    mem_jetSmallBallSet_circular N hN, Set.mem_inter_iff, circularPolynomialJetSmallBallEvent, Set.mem_ofPred_eq]

/-- Joint small-value events for a single Steinhaus polynomial factor up to the
explicit inverse-square-root error at separated annular points. -/
theorem exists_steinhaus_polynomial_small_ball_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) (u v u' v' : ℝ),
      |(Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
        (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v ∩
          circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v') -
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
          (circularPolynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) *
        (Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).real
          (circularPolynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v')| ≤
        (2 * circularJetGaussianErrorConstant C K + circularPairedJetGaussianErrorConstant C K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_annular_circular_jet_factorization_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum u v u' v'
  have hb := h N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (jetSmallBallSet u v) (jetSmallBallSet u' v')
    (measurableSet_jetSmallBallSet u v) (measurableSet_jetSmallBallSet u' v')
    (isConvexSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u' v')
  rwa [circularPairedJet_measureReal_smallBall N hN, circularJet_measureReal_smallBall N hN,
    circularJet_measureReal_smallBall N hN] at hb


end Erdos522

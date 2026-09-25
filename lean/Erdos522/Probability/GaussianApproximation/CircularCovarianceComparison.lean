/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularPairedJets
import Erdos522.Probability.GaussianApproximation.CircularJets
import Erdos522.Probability.GaussianApproximation.PairedSmallBall

/-!
# Covariance comparison for separated circular jets

Quarter turns preserve Euclidean norms and commute with the two-jet split.
Averaging the real covariance error in a direction and its quarter turn
therefore preserves the explicit covariance-comparison constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The adjoint quarter turn in the two complex coordinates of one jet. -/
def jetDirectionRotation (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 1, -x 0, x 3, -x 2]

theorem norm_jetDirectionRotation (x : EuclideanSpace ℝ (Fin 4)) :
    ‖jetDirectionRotation x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, jetDirectionRotation, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_sq]
  ring

theorem inner_imaginaryJetCoefficient_rotation (N : ℕ) (r : ℝ) (z : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪x, imaginaryJetCoefficient N r z k⟫ =
      ⟪jetDirectionRotation x, realJetCoefficient N r z k⟫ := by
  rw [inner_imaginaryJetCoefficient, inner_realJetCoefficient]
  simp only [jetDirectionRotation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem finAddEquivProd_pairedJetDirectionRotation (x : EuclideanSpace ℝ (Fin 8)) :
    EuclideanSpace.finAddEquivProd (n := 4) (m := 4) (pairedJetDirectionRotation x) =
      (jetDirectionRotation (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).1,
        jetDirectionRotation (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).2) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

theorem quadratic_circularCovarianceMatrix_jet (N : ℕ) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    x.ofLp ⬝ᵥ circularCovarianceMatrix (realJetCoefficient N r z)
      (imaginaryJetCoefficient N r z) *ᵥ x.ofLp =
      (x.ofLp ⬝ᵥ signCovarianceMatrix (realJetCoefficient N r z) *ᵥ x.ofLp +
        (jetDirectionRotation x).ofLp ⬝ᵥ signCovarianceMatrix (realJetCoefficient N r z) *ᵥ
          (jetDirectionRotation x).ofLp) / 2 := by
  rw [circularCovarianceMatrix_form, signCovarianceMatrix_form, signCovarianceMatrix_form]
  simp only [inner_imaginaryJetCoefficient_rotation, ← Finset.sum_div, Finset.sum_add_distrib]

theorem quadratic_circularCovarianceMatrix_pairedJet (N : ℕ) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ circularCovarianceMatrix (realPairedJetCoefficient N r s z w)
      (imaginaryPairedJetCoefficient N r s z w) *ᵥ x.ofLp =
      (x.ofLp ⬝ᵥ signCovarianceMatrix (realPairedJetCoefficient N r s z w) *ᵥ x.ofLp +
        (pairedJetDirectionRotation x).ofLp ⬝ᵥ signCovarianceMatrix (realPairedJetCoefficient N r s z w) *ᵥ
          (pairedJetDirectionRotation x).ofLp) / 2 := by
  rw [circularCovarianceMatrix_form, signCovarianceMatrix_form, signCovarianceMatrix_form]
  simp only [inner_imaginaryPairedJetCoefficient, ← Finset.sum_div, Finset.sum_add_distrib]

/-- The circular joint-to-independent covariance difference is the average
of the real differences in two norm-preserving directions. -/
theorem circularPairedJet_covariance_error_eq (N : ℕ) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ (circularCovarianceMatrix (realPairedJetCoefficient N r s z w)
        (imaginaryPairedJetCoefficient N r s z w) -
      gaussianBlockCovariance
        (circularCovarianceMatrix (realJetCoefficient N r z) (imaginaryJetCoefficient N r z))
        (circularCovarianceMatrix (realJetCoefficient N s w) (imaginaryJetCoefficient N s w))) *ᵥ x.ofLp =
      (x.ofLp ⬝ᵥ (signCovarianceMatrix (realPairedJetCoefficient N r s z w) -
        gaussianBlockCovariance (signCovarianceMatrix (realJetCoefficient N r z))
          (signCovarianceMatrix (realJetCoefficient N s w))) *ᵥ x.ofLp +
        (pairedJetDirectionRotation x).ofLp ⬝ᵥ (signCovarianceMatrix (realPairedJetCoefficient N r s z w) -
          gaussianBlockCovariance (signCovarianceMatrix (realJetCoefficient N r z))
            (signCovarianceMatrix (realJetCoefficient N s w))) *ᵥ (pairedJetDirectionRotation x).ofLp) / 2 := by
  simp only [Matrix.sub_mulVec, dotProduct_sub, quadratic_circularCovarianceMatrix_pairedJet,
    quadratic_gaussianBlockCovariance (m := 4) (n := 4), quadratic_circularCovarianceMatrix_jet,
    finAddEquivProd_pairedJetDirectionRotation]
  ring

/-- The circular covariance perturbation is bounded by the same quadratic
error `20 exp(4K)/sqrt N` as the real paired covariance. -/
theorem circularPairedJet_covariance_error_le (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    |x.ofLp ⬝ᵥ (circularCovarianceMatrix (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
        (imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) -
      gaussianBlockCovariance
        (circularCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
          (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ))))
        (circularCovarianceMatrix (realJetCoefficient N s (Complex.exp (Complex.I * φ)))
          (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ))))) *ᵥ x.ofLp| ≤
      (20 * Real.exp (4 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
  have h1 := pairedJet_covariance_error_le N hN K r s θ φ hK hr0 hs0 hr hs hdifference hsum x
  have h2 := pairedJet_covariance_error_le N hN K r s θ φ hK hr0 hs0 hr hs hdifference hsum
    (pairedJetDirectionRotation x)
  rw [norm_pairedJetDirectionRotation] at h2
  rw [circularPairedJet_covariance_error_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  linarith

/-- The Gaussian law of separated polynomial jets differs from its independent
marginals by at most the manuscript's explicit covariance-comparison constant. -/
theorem gaussian_circularPairedJet_measureReal_prod_le (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 4))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(multivariateGaussian 0 (circularCovarianceMatrix (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
      (multivariateGaussian 0 (circularCovarianceMatrix (realJetCoefficient N r
        (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r
        (Complex.exp (Complex.I * θ))))).real A *
      (multivariateGaussian 0 (circularCovarianceMatrix (realJetCoefficient N s
        (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s
        (Complex.exp (Complex.I * φ))))).real B| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  let S₁ := circularCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ))) (imaginaryJetCoefficient N r (Complex.exp (Complex.I * θ)))
  let S₂ := circularCovarianceMatrix (realJetCoefficient N s (Complex.exp (Complex.I * φ))) (imaginaryJetCoefficient N s (Complex.exp (Complex.I * φ)))
  let S := circularCovarianceMatrix (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) (imaginaryPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
  let c := Real.exp (-4 * K) / 80
  let δ := 20 * Real.exp (4 * K) / Real.sqrt N
  have hc : 0 < c := by dsimp [c]; positivity
  have hz : ‖Complex.exp (Complex.I * θ)‖ = 1 := Complex.norm_exp_I_mul_ofReal θ
  have hw : ‖Complex.exp (Complex.I * φ)‖ = 1 := Complex.norm_exp_I_mul_ofReal φ
  have hl₁ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₁ *ᵥ x.ofLp := by
    rw [circularCovarianceMatrix_form]
    have h := circular_jet_gram_lower N hN K r hK hNK hrl _ hz x
    simp only [sq] at h
    dsimp [c]
    have he := Real.exp_pos (-4 * K)
    nlinarith [sq_nonneg ‖x‖]
  have hl₂ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₂ *ᵥ x.ofLp := by
    rw [circularCovarianceMatrix_form]
    have h := circular_jet_gram_lower N hN K s hK hNK hsl _ hw x
    simp only [sq] at h
    dsimp [c]
    have he := Real.exp_pos (-4 * K)
    nlinarith [sq_nonneg ‖x‖]
  have h₁ : S₁.PosDef := circularCovarianceMatrix_posDef _ _ _ (by positivity)
    (circular_jet_gram_lower N hN K r hK hNK hrl _ hz)
  have h₂ : S₂.PosDef := circularCovarianceMatrix_posDef _ _ _ (by positivity)
    (circular_jet_gram_lower N hN K s hK hNK hsl _ hw)
  have hS : S.PosDef := circularPairedJetCovarianceMatrix_posDef N hN K r s θ φ hK hNK
    hrl hru hsl hsu hdegree hθ hφ hdifference hsum
  have hT := gaussianBlockCovariance_posDef_of_lower S₁ S₂ h₁.posSemidef h₂.posSemidef c hc hl₁ hl₂
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have herror := circularPairedJet_covariance_error_le N hN K r s θ φ hK hr0 hs0 hru hsu hdifference hsum
  have h := gaussian_measureReal_sub_le_eight S (gaussianBlockCovariance S₁ S₂) hS hT c δ hc
    (by dsimp [δ]; positivity) (pairedJet_relative_error_le_half N hN K hdegree)
    (gaussianBlockCovariance_lower S₁ S₂ c hl₁ hl₂) herror
    ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) ((hA.prod hB).preimage (by fun_prop))
  rw [gaussianBlockCovariance_measureReal_prod S₁ S₂ h₁.posSemidef h₂.posSemidef A B hA hB] at h
  refine h.trans ?_
  dsimp [c, δ]
  have hpos : 0 ≤ Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N) := by positivity
  calc
    _ = 40 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by ring
    _ ≤ 80 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by nlinarith
    _ = _ := by ring


end Erdos522

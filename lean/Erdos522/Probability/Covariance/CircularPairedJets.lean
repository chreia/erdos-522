/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.CircularJets
import Erdos522.Probability.Covariance.JetMoments

/-!
# Circular covariance for a separated pair of jets

The imaginary coefficient contribution is a quarter turn in each complex
coordinate. The circular covariance averages two real paired Gram forms, so
the separated-pair lower bound is retained without a loss in its constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The adjoint quarter turn on four complex coordinates represented over `ℝ`. -/
def pairedJetDirectionRotation (x : EuclideanSpace ℝ (Fin 8)) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 ![x 1, -x 0, x 3, -x 2, x 5, -x 4, x 7, -x 6]

theorem norm_pairedJetDirectionRotation (x : EuclideanSpace ℝ (Fin 8)) :
    ‖pairedJetDirectionRotation x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, pairedJetDirectionRotation,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- The coefficient contributed by the imaginary part to both normalized jets. -/
def imaginaryPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 8) :=
  let a := realPairedJetCoefficient N r s z w k
  WithLp.toLp 2 ![-a 1, a 0, -a 3, a 2, -a 5, a 4, -a 7, a 6]

theorem norm_imaginaryPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ) (k : Fin (N + 1)) :
    ‖imaginaryPairedJetCoefficient N r s z w k‖ = ‖realPairedJetCoefficient N r s z w k‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, imaginaryPairedJetCoefficient,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

/-- Rotating the direction transfers the imaginary Gram form to the real one. -/
theorem inner_imaginaryPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 8)) :
    ⟪x, imaginaryPairedJetCoefficient N r s z w k⟫ =
      ⟪pairedJetDirectionRotation x, realPairedJetCoefficient N r s z w k⟫ := by
  simp only [imaginaryPairedJetCoefficient, pairedJetDirectionRotation, PiLp.inner_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, RCLike.inner_apply, conj_trivial]
  norm_num
  ring

/-- Both circular jets are evaluated using the same complex coefficient vector. -/
def circularPairedJet (N : ℕ) (r s : ℝ) (z w : ℂ) :
    (Fin (N + 1) → ℂ) → EuclideanSpace ℝ (Fin 8) :=
  circularVectorSum (realPairedJetCoefficient N r s z w) (imaginaryPairedJetCoefficient N r s z w)

/-- The circular paired covariance is the average of two rotated real Gram forms. -/
theorem covarianceBilin_circularPairedJet (N : ℕ) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    covarianceBilin ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
      (circularPairedJet N r s z w)) x x =
      ((∑ k, ⟪x, realPairedJetCoefficient N r s z w k⟫ ^ 2) +
        ∑ k, ⟪pairedJetDirectionRotation x, realPairedJetCoefficient N r s z w k⟫ ^ 2) / 2 := by
  rw [circularPairedJet, covarianceBilin_circularVectorSum]
  simp only [← sq, inner_imaginaryPairedJetCoefficient, ← Finset.sum_div, Finset.sum_add_distrib]

/-- The actual eight-dimensional Steinhaus jet covariance retains the
separated-pair constant `exp(-4K)/160`. -/
theorem covarianceBilin_circularPairedJet_lower (N : ℕ) (hN : 0 < N)
    (K r s θ φ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    (Real.exp (-4 * K) / 160) * ‖x‖ ^ 2 ≤ covarianceBilin
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map (circularPairedJet N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) x x := by
  have h1 := covarianceBilin_realPairedRademacherJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum x
  have h2 := covarianceBilin_realPairedRademacherJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum (pairedJetDirectionRotation x)
  simp only [realPairedRademacherJet, covarianceBilin_signVectorSum, ← sq] at h1 h2
  rw [norm_pairedJetDirectionRotation] at h2
  rw [covarianceBilin_circularPairedJet]
  linarith

/-- The same nondegeneracy in the coefficient Gram form used by Bentkus. -/
theorem circular_paired_jet_gram_lower (N : ℕ) (hN : 0 < N)
    (K r s θ φ : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    (Real.exp (-4 * K) / 160) * ‖x‖ ^ 2 ≤
      ∑ k, (⟪x, realPairedJetCoefficient N r s (Complex.exp (Complex.I * θ))
        (Complex.exp (Complex.I * φ)) k⟫ ^ 2 +
        ⟪x, imaginaryPairedJetCoefficient N r s (Complex.exp (Complex.I * θ))
          (Complex.exp (Complex.I * φ)) k⟫ ^ 2) / 2 := by
  have h := covarianceBilin_circularPairedJet_lower N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum x
  simpa only [circularPairedJet, covarianceBilin_circularVectorSum, sq] using h

end Erdos522

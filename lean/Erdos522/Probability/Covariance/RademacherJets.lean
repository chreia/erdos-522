/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.CrossCovariance
import Erdos522.Probability.RademacherCoordinates
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance laws of finite Rademacher jets

Independent fair signs turn deterministic coefficient Gram forms into
covariances. This identifies the annular jet forms with the native covariance
bilinear form of the normalized random value and derivative vectors.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace Erdos522
open LogMoments

/-- A real linear combination of the coordinate signs. -/
def signLinear {N : ℕ} (a : Fin (N + 1) → ℝ) (ω : SignVector N) : ℝ :=
  ∑ k, a k * realSign (ω k)

/-- A coordinate sign has the identity covariance matrix. -/
theorem covariance_realSign_coordinates {N : ℕ} (i j : Fin (N + 1)) :
    cov[fun ω : SignVector N => realSign (ω i), fun ω => realSign (ω j); signMeasure N] =
      if i = j then 1 else 0 := by
  rw [covariance]
  simp only [integral_realSign_coordinate, sub_zero]
  exact integral_mul_realSign_coordinates i j

/-- The covariance of two real linear combinations of independent signs. -/
theorem covariance_signLinear {N : ℕ} (a b : Fin (N + 1) → ℝ) :
    cov[signLinear a, signLinear b; signMeasure N] = ∑ k, a k * b k := by
  unfold signLinear
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_realSign_coordinates]
    simp
  all_goals exact fun _ => MemLp.of_discrete

/-- A finite random vector whose summands use the shared product sign law. -/
def signVectorSum {N : ℕ} {d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (ω : SignVector N) : EuclideanSpace ℝ (Fin d) :=
  ∑ k, realSign (ω k) • a k

/-- Real projection of a vector sign sum is the corresponding scalar sign sum. -/
theorem inner_signVectorSum {N d : ℕ} (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ω : SignVector N) :
    ⟪x, signVectorSum a ω⟫ = signLinear (fun k => ⟪x, a k⟫) ω := by
  simp only [signVectorSum, signLinear, inner_sum, real_inner_smul_right, mul_comm]

/-- The native covariance bilinear form of a vector sign sum is its coefficient Gram form. -/
theorem covarianceBilin_signVectorSum {N d : ℕ}
    (a : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    covarianceBilin ((signMeasure N).map (signVectorSum a)) x y =
      ∑ k, ⟪x, a k⟫ * ⟪y, a k⟫ := by
  have ha : MemLp (signVectorSum a) 2 (signMeasure N) := MemLp.of_discrete
  have hm : MemLp id 2 ((signMeasure N).map (signVectorSum a)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_of_finite _).aemeasurable).mpr ha
  rw [covarianceBilin_apply_eq_cov hm, covariance_map_fun]
  · simpa only [inner_signVectorSum] using
      covariance_signLinear (fun k => ⟪x, a k⟫) (fun k => ⟪y, a k⟫)
  all_goals fun_prop

/-- The coefficient vector of the normalized value-derivative jet at one point. -/
def realJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![r ^ k.val / Real.sqrt N * (z ^ k.val).re,
    r ^ k.val / Real.sqrt N * (z ^ k.val).im,
    r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).re,
    r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).im]

/-- The normalized four-dimensional real jet under the shared product sign law. -/
def realRademacherJet (N : ℕ) (r : ℝ) (z : ℂ) : SignVector N → EuclideanSpace ℝ (Fin 4) :=
  signVectorSum (realJetCoefficient N r z)

/-- The projection of one jet coefficient in a real Euclidean direction. -/
theorem inner_realJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪x, realJetCoefficient N r z k⟫ = (r ^ k.val / Real.sqrt N) *
      ((x 0 + (k.val : ℝ) / N * x 2) * (z ^ k.val).re +
        (x 1 + (k.val : ℝ) / N * x 3) * (z ^ k.val).im) := by
  simp only [realJetCoefficient, PiLp.inner_apply, Fin.sum_univ_four,
    RCLike.inner_apply, conj_trivial]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- The deterministic jet form equals the covariance of the normalized Rademacher jet. -/
theorem covarianceBilin_realRademacherJet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    covarianceBilin ((signMeasure N).map (realRademacherJet N r z)) x x =
      realJetCovarianceForm N r z x := by
  have hn : (0 : ℝ) ≤ N := by positivity
  rw [realRademacherJet, covarianceBilin_signVectorSum]
  simp_rw [← pow_two, inner_realJetCoefficient, mul_pow, div_pow, Real.sq_sqrt hn]
  unfold realJetCovarianceForm
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← pow_mul, mul_comm k.val 2]
  ring

/-- The finite Rademacher jet law has the manuscript's explicit covariance lower bound. -/
theorem covarianceBilin_realRademacherJet_lower (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 4)) :
    (Real.exp (-4 * K) / 80) * ‖x‖ ^ 2 ≤
      covarianceBilin ((signMeasure N).map
        (realRademacherJet N r (Complex.exp (Complex.I * θ)))) x x := by
  rw [covarianceBilin_realRademacherJet N hN]
  exact real_annular_jet_nondegeneracy N hN K r θ hK hNK hrl hru hdegree hangle x

/-- A coefficient of the pair of normalized real value-derivative jets. -/
def realPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 ![r ^ k.val / Real.sqrt N * (z ^ k.val).re,
    r ^ k.val / Real.sqrt N * (z ^ k.val).im,
    r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).re,
    r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).im,
    s ^ k.val / Real.sqrt N * (w ^ k.val).re,
    s ^ k.val / Real.sqrt N * (w ^ k.val).im,
    s ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (w ^ k.val).re,
    s ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (w ^ k.val).im]

/-- The normalized pair of real jets uses the same signs at both points. -/
def realPairedRademacherJet (N : ℕ) (r s : ℝ) (z w : ℂ) :
    SignVector N → EuclideanSpace ℝ (Fin 8) := signVectorSum (realPairedJetCoefficient N r s z w)

/-- The projection of a paired jet coefficient in an eight-dimensional direction. -/
theorem inner_realPairedJetCoefficient (N : ℕ) (r s : ℝ) (z w : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 8)) :
    ⟪x, realPairedJetCoefficient N r s z w k⟫ = (1 / Real.sqrt N) *
      (r ^ k.val * ((x 0 + (k.val : ℝ) / N * x 2) * (z ^ k.val).re +
        (x 1 + (k.val : ℝ) / N * x 3) * (z ^ k.val).im) +
      s ^ k.val * ((x 4 + (k.val : ℝ) / N * x 6) * (w ^ k.val).re +
        (x 5 + (k.val : ℝ) / N * x 7) * (w ^ k.val).im)) := by
  simp only [realPairedJetCoefficient, PiLp.inner_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, RCLike.inner_apply, conj_trivial]
  norm_num
  ring

/-- The deterministic paired form is the native covariance of the joint Rademacher law. -/
theorem covarianceBilin_realPairedRademacherJet (N : ℕ) (hN : 0 < N) (r s : ℝ)
    (z w : ℂ) (x : EuclideanSpace ℝ (Fin 8)) :
    covarianceBilin ((signMeasure N).map (realPairedRademacherJet N r s z w)) x x =
      realPairedJetCovarianceForm N r s z w x := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [realPairedRademacherJet, covarianceBilin_signVectorSum]
  simp_rw [← pow_two, inner_realPairedJetCoefficient, mul_pow, div_pow, Real.sq_sqrt hn.le]
  unfold realPairedJetCovarianceForm
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  norm_num

/-- The actual eight-dimensional finite Rademacher jet law is nondegenerate
at separated annular points. -/
theorem covarianceBilin_realPairedRademacherJet_lower (N : ℕ) (hN : 0 < N)
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
      ((signMeasure N).map (realPairedRademacherJet N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))) x x := by
  rw [covarianceBilin_realPairedRademacherJet N hN]
  exact real_paired_annular_jet_nondegeneracy N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum x

end Erdos522

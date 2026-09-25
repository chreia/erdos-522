/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.CircularVectors

/-!
# Circular value-derivative jets

Circular symmetry cancels the oscillatory covariance correction at a single
point. The remaining form is the weighted affine index energy, giving a
uniform lower bound throughout the annulus at every angle.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Erdos522

/-- The jet coefficient contributed by the imaginary part of a coefficient. -/
def imaginaryJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![-(r ^ k.val / Real.sqrt N * (z ^ k.val).im),
    r ^ k.val / Real.sqrt N * (z ^ k.val).re,
    -(r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).im),
    r ^ k.val / Real.sqrt N * ((k.val : ℝ) / N) * (z ^ k.val).re]

/-- The normalized circular jet on the finite coefficient space. -/
def circularJet (N : ℕ) (r : ℝ) (z : ℂ) :
    (Fin (N + 1) → ℂ) → EuclideanSpace ℝ (Fin 4) :=
  circularVectorSum (realJetCoefficient N r z) (imaginaryJetCoefficient N r z)

theorem norm_imaginaryJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ) (k : Fin (N + 1)) :
    ‖imaginaryJetCoefficient N r z k‖ = ‖realJetCoefficient N r z k‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four,
    imaginaryJetCoefficient, realJetCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_sq]
  ring

theorem inner_imaginaryJetCoefficient (N : ℕ) (r : ℝ) (z : ℂ)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪x, imaginaryJetCoefficient N r z k⟫ = (r ^ k.val / Real.sqrt N) *
      (-(x 0 + (k.val : ℝ) / N * x 2) * (z ^ k.val).im +
        (x 1 + (k.val : ℝ) / N * x 3) * (z ^ k.val).re) := by
  simp only [imaginaryJetCoefficient, PiLp.inner_apply, Fin.sum_univ_four,
    RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- The sum of the two coordinate Gram squares loses its angular dependence. -/
theorem circular_jet_gram_squares (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (k : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪x, realJetCoefficient N r z k⟫ ^ 2 +
      ⟪x, imaginaryJetCoefficient N r z k⟫ ^ 2 =
      r ^ (2 * k.val) / N * ((x 0 + (k.val : ℝ) / N * x 2) ^ 2 +
        (x 1 + (k.val : ℝ) / N * x 3) ^ 2) := by
  have hphase : (z ^ k.val).re ^ 2 + (z ^ k.val).im ^ 2 = 1 := by
    calc
      _ = ‖z ^ k.val‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by simp [norm_pow, hz]
  rw [inner_realJetCoefficient, inner_imaginaryJetCoefficient]
  rw [show 2 * k.val = k.val * 2 by omega, pow_mul]
  have hfactor (a b u v s : ℝ) :
      (s * (a * u + b * v)) ^ 2 + (s * (-a * v + b * u)) ^ 2 =
        s ^ 2 * (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by ring
  rw [hfactor, hphase, mul_one, div_pow, Real.sq_sqrt (by positivity)]

/-- Exact circular covariance as weighted affine index energy. -/
theorem covarianceBilin_circularJet (N : ℕ) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (x : EuclideanSpace ℝ (Fin 4)) :
    covarianceBilin ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
      (circularJet N r z)) x x =
      (1 / (2 * N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        r ^ (2 * k) * ((x 0 + (k : ℝ) / N * x 2) ^ 2 +
          (x 1 + (k : ℝ) / N * x 3) ^ 2) := by
  unfold circularJet
  rw [covarianceBilin_circularVectorSum]
  simp_rw [← sq, circular_jet_gram_squares N r z hz]
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Circular jet nondegeneracy holds at every angle in the annulus. -/
theorem annular_circular_jet_nondegeneracy (N : ℕ) (hN : 0 < N) (K r : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hrl : 1 - K / N ≤ r)
    (z : ℂ) (hz : ‖z‖ = 1) (x : EuclideanSpace ℝ (Fin 4)) :
    (Real.exp (-4 * K) / 32) * ‖x‖ ^ 2 ≤
      covarianceBilin ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).map
        (circularJet N r z)) x x := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ r := by
    have hu : K / N ≤ (1 / 2 : ℝ) := (div_le_iff₀ hn).mpr (by linarith)
    linarith
  have hw (k : ℕ) (hk : k ≤ N) : Real.exp (-4 * K) ≤ r ^ (2 * k) :=
    radial_square_power_lower N k hN hk K r hK hNK hr0 hrl
  have hre := weighted_index_energy_lower N hN (fun k => r ^ (2 * k))
    (Real.exp (-4 * K)) (by positivity) hw (x 0) (x 2)
  have him := weighted_index_energy_lower N hN (fun k => r ^ (2 * k))
    (Real.exp (-4 * K)) (by positivity) hw (x 1) (x 3)
  rw [covarianceBilin_circularJet N r z hz, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_four]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ ((1 / N) * ∑ k ∈ Finset.range (N + 1), r ^ (2 * k) *
        (x 0 + (k : ℝ) / N * x 2) ^ 2 +
      (1 / N) * ∑ k ∈ Finset.range (N + 1), r ^ (2 * k) *
        (x 1 + (k : ℝ) / N * x 3) ^ 2) / 2 := by nlinarith only [hre, him]
    _ = _ := by ring

end Erdos522

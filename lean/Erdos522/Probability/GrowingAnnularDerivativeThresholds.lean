/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Limits.LogarithmicAnnularScales

/-!
# Mesh thresholds on a growing annulus

The expected mesh count and the excised-sector contribution are smaller than
`N^(31/32)` at logarithmic annular width. Each limit follows from an explicit
positive power margin, with the width retained in the finite inequalities.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos522

/-- The one-point mesh detection probability tends to zero at logarithmic width. -/
theorem tendsto_growing_annular_jet_probability {C : ℝ} (hC : 0 < C) :
    Tendsto (fun N : ℕ =>
      annularJetProbabilityBound N C (logarithmicAnnularWidth N)
        (derivativeMeshValueThreshold N (annularDerivativeScale (logarithmicAnnularWidth N))
          ((N : ℝ) ^ (1 / 64 : ℝ))) (3 / (N : ℝ) ^ (1 / 64 : ℝ))) atTop (𝓝 0) := by
  let a := annularJetDensityCoefficient 0 (annularDerivativeScale 0)
  let b := jetGaussianErrorConstant C 0
  have ha : 0 ≤ a := by unfold a annularJetDensityCoefficient; positivity
  have hb : 0 ≤ b := (jetGaussianErrorConstant_pos C 0 hC).le
  have h₁ := (tendsto_logarithmicAnnularWidth_factor (a := 6) (b := 3 / 32)
    (by norm_num) (by norm_num) 0 0).const_mul a
  have h₂ := (tendsto_logarithmicAnnularWidth_factor (a := 9) (b := 1 / 2)
    (by norm_num) (by norm_num) 0 0).const_mul b
  have ht := h₁.add h₂
  simp only [pow_zero, one_mul, mul_one, mul_zero, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 2] with N _
    unfold annularJetProbabilityBound
    have := jetGaussianErrorConstant_pos C (logarithmicAnnularWidth N) hC
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1, eventually_ge_atTop 2] with N hlog hN
    have hl : 1 ≤ Real.log N := hlog
    have hK := logarithmicAnnularWidth_nonneg N
    have hS := one_le_annularDerivativeScale hK
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [annularJetProbabilityBound_power_eq (by omega) (by linarith : 0 < annularDerivativeScale (logarithmicAnnularWidth N)),
      annularJetDensityCoefficient_eq_exp, jetGaussianErrorConstant_eq_exp,
      show (-3 / 32 : ℝ) = -(3 / 32 : ℝ) by ring,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn.le, Real.rpow_neg hn.le]
    calc
      _ ≤ (a * Real.exp (6 * logarithmicAnnularWidth N) * ((N : ℝ) ^ (3 / 32 : ℝ))⁻¹) / 1 +
          b * Real.exp (9 * logarithmicAnnularWidth N) * ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
        gcongr
      _ = _ := by ring

/-- The finite normalized mesh mean is bounded by two explicit width factors. -/
theorem growing_annular_mean_ratio_le {N : ℕ} (hN : 2 ≤ N) {C : ℝ} (hC : 0 < C) :
    let K := logarithmicAnnularWidth N
    let S := annularDerivativeScale K
    (annularMeshSizeConstant K S * N * ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N *
        annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ))) *
      (4 * LocalZeroCount.localCountConstant (K + 2) * Real.log N) / (N : ℝ) ^ (31 / 32 : ℝ) ≤
    4 * LocalZeroCount.localCountConstant 2 * annularMeshSizeConstant 0 (annularDerivativeScale 0) *
      annularJetDensityCoefficient 0 (annularDerivativeScale 0) *
        ((K + 1) ^ 2 * Real.exp (8 * K) * Real.log N / (N : ℝ) ^ (1 / 32 : ℝ)) +
    4 * LocalZeroCount.localCountConstant 2 * annularMeshSizeConstant 0 (annularDerivativeScale 0) *
      jetGaussianErrorConstant C 0 *
        ((K + 1) ^ 2 * Real.exp (11 * K) * (Real.log N) ^ 2 / (N : ℝ) ^ (7 / 16 : ℝ)) := by
  dsimp only
  let K := logarithmicAnnularWidth N
  have hK : 0 ≤ K := logarithmicAnnularWidth_nonneg N
  have hS := one_le_annularDerivativeScale hK
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hc : 0 ≤ LocalZeroCount.localCountConstant (K + 2) := by
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  have ha : 0 ≤ annularJetDensityCoefficient 0 (annularDerivativeScale 0) := by
    unfold annularJetDensityCoefficient
    positivity
  have hb := (jetGaussianErrorConstant_pos C 0 hC).le
  have hD : 0 ≤ annularMeshSizeConstant 0 (annularDerivativeScale 0) := by
    unfold annularMeshSizeConstant; positivity
  rw [annularJetProbabilityBound_power_eq (by omega) (by linarith : 0 < annularDerivativeScale (logarithmicAnnularWidth N))]
  rw [annular_mean_ratio_identity hn]
  rw [annularMeshSizeConstant_eq_exp, annularJetDensityCoefficient_eq_exp, jetGaussianErrorConstant_eq_exp]
  calc
    _ ≤ 4 * (LocalZeroCount.localCountConstant 2 * (K + 1)) *
          (annularMeshSizeConstant 0 (annularDerivativeScale 0) * (K + 1) * Real.exp (2 * K)) *
          (annularJetDensityCoefficient 0 (annularDerivativeScale 0) * Real.exp (6 * K)) *
          Real.log N / (N : ℝ) ^ (1 / 32 : ℝ) +
        4 * (LocalZeroCount.localCountConstant 2 * (K + 1)) *
          (annularMeshSizeConstant 0 (annularDerivativeScale 0) * (K + 1) * Real.exp (2 * K)) *
          (jetGaussianErrorConstant C 0 * Real.exp (9 * K)) *
          (Real.log N) ^ 2 / (N : ℝ) ^ (7 / 16 : ℝ) := by
      gcongr <;> exact localCountConstant_width_le hK
    _ = _ := by
      rw [show (8 : ℝ) * logarithmicAnnularWidth N = 2 * K + 6 * K by dsimp [K]; ring,
        show (11 : ℝ) * logarithmicAnnularWidth N = 2 * K + 9 * K by dsimp [K]; ring,
        Real.exp_add, Real.exp_add]
      dsimp [K]
      ring

/-- The normalized mesh mean tends to zero with its actual local-count constants. -/
theorem tendsto_growing_annular_mean_ratio {C : ℝ} (hC : 0 < C) :
    Tendsto (fun N : ℕ =>
      let K := logarithmicAnnularWidth N
      let S := annularDerivativeScale K
      (annularMeshSizeConstant K S * N * ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N *
        annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ))) *
        (4 * LocalZeroCount.localCountConstant (K + 2) * Real.log N) / (N : ℝ) ^ (31 / 32 : ℝ))
      atTop (𝓝 0) := by
  have h₁ := (tendsto_logarithmicAnnularWidth_factor (a := 8) (b := 1 / 32)
    (by norm_num) (by norm_num) 2 1).const_mul
    (4 * LocalZeroCount.localCountConstant 2 * annularMeshSizeConstant 0 (annularDerivativeScale 0) *
      annularJetDensityCoefficient 0 (annularDerivativeScale 0))
  have h₂ := (tendsto_logarithmicAnnularWidth_factor (a := 11) (b := 7 / 16)
    (by norm_num) (by norm_num) 2 2).const_mul
    (4 * LocalZeroCount.localCountConstant 2 * annularMeshSizeConstant 0 (annularDerivativeScale 0) *
      jetGaussianErrorConstant C 0)
  have ht := h₁.add h₂
  simp only [mul_zero, add_zero, pow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hj := (jetGaussianErrorConstant_pos C (logarithmicAnnularWidth N) hC).le
    dsimp only
    unfold annularJetProbabilityBound annularMeshSizeConstant LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact growing_annular_mean_ratio_le hN hC

/-- The excised-sector contribution is smaller than the target root count. -/
theorem tendsto_growing_annular_sector_ratio :
    Tendsto (fun N : ℕ => 80 * LocalZeroCount.localCountConstant (logarithmicAnnularWidth N + 2) *
      Real.log N * Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ)) atTop (𝓝 0) := by
  have ht := (tendsto_logarithmicAnnularWidth_factor (a := 0) (b := 15 / 32)
    (by norm_num) (by norm_num) 1 1).const_mul (80 * LocalZeroCount.localCountConstant 2)
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hK := logarithmicAnnularWidth_nonneg N
    have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    calc
      _ ≤ 80 * (LocalZeroCount.localCountConstant 2 * (logarithmicAnnularWidth N + 1)) *
          Real.log N * Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ) := by
        gcongr
        exact localCountConstant_width_le (logarithmicAnnularWidth_nonneg N)
      _ = _ := by
        have hp : Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ) = 1 / (N : ℝ) ^ (15 / 32 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn]
          norm_num
          simp only [Real.rpow_neg hn.le]
        calc
          _ = 80 * LocalZeroCount.localCountConstant 2 *
              ((logarithmicAnnularWidth N + 1) * Real.log N) *
              (Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ)) := by ring
          _ = _ := by rw [hp]; ring

end Erdos522

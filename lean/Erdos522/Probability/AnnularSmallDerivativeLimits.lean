/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries

/-!
# Eventual annular small-derivative bounds

For fixed annular widths, every scalar condition in the finite-degree bound
holds eventually. Logarithmic factors are dominated by the positive gaps
between the powers in the expected count, sector count, and target count.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The Gaussian density coefficient after substitution of the mesh thresholds. -/
def annularJetDensityCoefficient (K S : ℝ) : ℝ :=
  9 / (1024 * S ^ 2 * (Real.exp (-4 * K) / 80) ^ 2)

/-- Substitution of the two mesh thresholds into the joint small-ball probability. -/
theorem annularJetProbabilityBound_eq {N : ℕ} (hN : 1 < N) {S L : ℝ}
    (hS : 0 < S) (hL : 0 < L) (C K : ℝ) :
    annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S L) (3 / L) =
      annularJetDensityCoefficient K S / (L ^ 6 * Real.log N) +
        jetGaussianErrorConstant C K / Real.sqrt N := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsqrt : Real.sqrt (Real.log N) ^ 2 = Real.log N := Real.sq_sqrt hlog.le
  unfold annularJetProbabilityBound derivativeMeshValueThreshold annularJetDensityCoefficient
  congr 1
  field_simp
  rw [hsqrt]
  ring

/-- Logarithmic factors of any fixed natural order are dominated by every positive power. -/
theorem tendsto_log_pow_div_nat_rpow (m : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (Real.log N) ^ m / (N : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hs).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_natCast] using h.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A negative power of a natural variable tends to zero. -/
theorem tendsto_nat_rpow_neg {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-s)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The density contribution at the chosen derivative scale has its exact power. -/
theorem annularJetProbabilityBound_power_eq {N : ℕ} (hN : 1 < N) {S : ℝ} (hS : 0 < S)
    (C K : ℝ) :
    annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
        (3 / (N : ℝ) ^ (1 / 64 : ℝ)) =
      annularJetDensityCoefficient K S * (N : ℝ) ^ (-3 / 32 : ℝ) / Real.log N +
        jetGaussianErrorConstant C K * (N : ℝ) ^ (-1 / 2 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [annularJetProbabilityBound_eq hN hS (Real.rpow_pos_of_pos hNr _) C K]
  have hL : ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 6 = (N : ℝ) ^ (3 / 32 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNr.le]
    congr 1
    norm_num
  rw [hL, Real.sqrt_eq_rpow, show (-3 / 32 : ℝ) = -(3 / 32 : ℝ) by ring,
    show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hNr.le, Real.rpow_neg hNr.le]
  ring

/-- The normalized deterministic upper bound on the mean mesh count separates into two decaying terms. -/
theorem annular_mean_ratio_identity {x c d a b : ℝ} (hx : 0 < x) :
    (d * x * (x ^ (1 / 64 : ℝ)) ^ 2 * Real.log x *
      (a * x ^ (-3 / 32 : ℝ) / Real.log x + b * x ^ (-1 / 2 : ℝ))) *
      (4 * c * Real.log x) / x ^ (31 / 32 : ℝ) =
    4 * c * d * a * Real.log x / x ^ (1 / 32 : ℝ) +
      4 * c * d * b * (Real.log x) ^ 2 / x ^ (7 / 16 : ℝ) := by
  by_cases hlog : Real.log x = 0
  · simp [hlog]
  have hL : (x ^ (1 / 64 : ℝ)) ^ 2 = x ^ (1 / 32 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  have hp₁ : x * x ^ (1 / 32 : ℝ) * x ^ (-3 / 32 : ℝ) / x ^ (31 / 32 : ℝ) =
      1 / x ^ (1 / 32 : ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx]
    norm_num
    simp only [Real.rpow_neg hx.le, one_div]
  have hp₂ : x * x ^ (1 / 32 : ℝ) * x ^ (-1 / 2 : ℝ) / x ^ (31 / 32 : ℝ) =
      1 / x ^ (7 / 16 : ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx]
    norm_num
    simp only [Real.rpow_neg hx.le]
  rw [hL]
  calc
    _ = 4 * c * d * a * Real.log x *
        (x * x ^ (1 / 32 : ℝ) * x ^ (-3 / 32 : ℝ) / x ^ (31 / 32 : ℝ)) +
      4 * c * d * b * (Real.log x) ^ 2 *
        (x * x ^ (1 / 32 : ℝ) * x ^ (-1 / 2 : ℝ) / x ^ (31 / 32 : ℝ)) := by
      field_simp
    _ = _ := by rw [hp₁, hp₂]; ring

/-- The specialized one-point jet probability bound tends to zero. -/
theorem tendsto_annularJetProbabilityBound {S : ℝ} (hS : 0 < S) (C K : ℝ) :
    Tendsto (fun N : ℕ => annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
        (3 / (N : ℝ) ^ (1 / 64 : ℝ))) atTop (𝓝 0) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have h₁ := (tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 3 / 32)).mul hlog
  have h₂ := tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : Tendsto (fun N : ℕ =>
      annularJetDensityCoefficient K S * (N : ℝ) ^ (-3 / 32 : ℝ) / Real.log N +
        jetGaussianErrorConstant C K * (N : ℝ) ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_def, Pi.inv_apply, neg_div, div_eq_mul_inv, neg_mul, mul_assoc] using
      (h₁.const_mul (annularJetDensityCoefficient K S)).add
        (h₂.const_mul (jetGaussianErrorConstant C K))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (annularJetProbabilityBound_power_eq (by omega : 1 < N) hS C K).symm

/-- The normalized upper bound for the expected mesh count tends to zero. -/
theorem tendsto_annular_mean_ratio {S : ℝ} (hS : 0 < S) (C K c : ℝ) :
    Tendsto (fun N : ℕ =>
      (annularMeshSizeConstant K S * N * ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N *
        annularJetProbabilityBound N C K
          (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
            (3 / (N : ℝ) ^ (1 / 64 : ℝ))) *
        (4 * c * Real.log N) / (N : ℝ) ^ (31 / 32 : ℝ)) atTop (𝓝 0) := by
  have h₁ := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 32)).const_mul
    (4 * c * annularMeshSizeConstant K S * annularJetDensityCoefficient K S)
  have h₂ := (tendsto_log_pow_div_nat_rpow 2 (by norm_num : (0 : ℝ) < 7 / 16)).const_mul
    (4 * c * annularMeshSizeConstant K S * jetGaussianErrorConstant C K)
  have ht := h₁.add h₂
  simp only [mul_zero, add_zero, pow_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [annularJetProbabilityBound_power_eq (by omega : 1 < N) hS C K]
  convert (annular_mean_ratio_identity (x := (N : ℝ))
    (by exact_mod_cast (show 0 < N by omega))).symm using 1
  ring

/-- The real-sector contribution is asymptotically smaller than the root-count threshold. -/
theorem tendsto_annular_sector_ratio (c : ℝ) :
    Tendsto (fun N : ℕ => 80 * c * Real.log N * Real.sqrt N /
      (N : ℝ) ^ (31 / 32 : ℝ)) atTop (𝓝 0) := by
  have ht := (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 15 / 32)).const_mul (80 * c)
  simp only [mul_zero, pow_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ) = 1 / (N : ℝ) ^ (15 / 32 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn]
    norm_num
    simp only [Real.rpow_neg hn.le]
  rw [show 80 * c * Real.log N * Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ) =
      80 * c * Real.log N * (Real.sqrt N / (N : ℝ) ^ (31 / 32 : ℝ)) by ring, hp]
  ring

/-- For fixed widths, the mean and sector thresholds in the quantitative root bound hold eventually. -/
theorem eventually_annular_small_derivative_scalar_bounds {K K' C : ℝ}
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      annularJetProbabilityBound N C K
        (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤ 1 ∧
      (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) *
        annularJetProbabilityBound N C K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
            (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤
        (N : ℝ) ^ (31 / 32 : ℝ) / (4 * LocalZeroCount.localCountConstant K' * Real.log N) ∧
      40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant K'
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hSp : 0 < S := by linarith
  have hc : 0 < c := by
    have hK' : 0 ≤ K' := by linarith
    dsimp [c, LocalZeroCount.localCountConstant, ArcEnergy.arcScale]
    positivity
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_annularJetProbabilityBound hSp C K).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_mean_ratio hSp C K c).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_sector_ratio c).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
      with N hN hp hmean hsector
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have hpow : 0 < (N : ℝ) ^ (31 / 32 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 1 ≤ (N : ℝ) ^ (1 / 64 : ℝ) := Real.one_le_rpow hn.le (by norm_num)
  have hprob : 0 ≤ annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ (1 / 64 : ℝ)))
        (3 / (N : ℝ) ^ (1 / 64 : ℝ)) := by
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos C K hC
    positivity
  refine ⟨hp.le, ?_, ?_⟩
  · have hcard := annular_mesh_cardinality_le (K := K) hN hK hS hL
    have hc' : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N S ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) ≤
        annularMeshSizeConstant K S * N * ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N := by
      simpa only [annularMeshSizeConstant, mul_assoc] using hcard
    apply (mul_le_mul_of_nonneg_right hc' hprob).trans
    apply (le_div_iff₀ (show 0 < 4 * c * Real.log N by positivity)).mpr
    simpa only [one_mul] using ((div_lt_one hpow).mp hmean).le
  · have hsector' := (div_lt_one hpow).mp hsector
    dsimp [annularLocalMultiplicityBound]
    dsimp [c] at hsector'
    linarith

/-- Fixed annular widths admit an unconditional eventual quantitative small-derivative estimate. -/
theorem eventually_annular_small_derivative_probability (K K' : ℝ)
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (LogMoments.signMeasure N).real {ω | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 + C *
        (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_annular_small_derivative_failure_constants
  let C := annularSmallDerivativeFailureConstant C₂ K K'
  have hC : 0 < C := by
    have hK' : 0 ≤ K' := by linarith
    have hV := annularJetPairConstant_pos C₂ K hC₂
    dsimp [C, annularSmallDerivativeFailureConstant, annularMeshSizeConstant,
      LocalZeroCount.localCountConstant, ArcEnergy.arcScale, annularDerivativeScale]
    positivity
  refine ⟨C, hC, ?_⟩
  have hwidth : Tendsto (fun N : ℕ => ArcEnergy.arcScale * Real.log N / N) atTop (𝓝 0) := by
    simpa only [pow_one, Real.rpow_one, mul_zero, mul_div_assoc] using
      (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1)).const_mul ArcEnergy.arcScale
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K + 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((6400 * Real.exp (8 * K)) ^ 2),
    hwidth.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_annular_small_derivative_scalar_bounds hK hKK' hC₁]
      with N hN hKN hKN' hdegree hwidthN hscalar
  exact hprob N hN K K' hK hKN hKN' hKK' hwidthN.le hdegree hscalar.1 hscalar.2.1 hscalar.2.2

end Erdos522

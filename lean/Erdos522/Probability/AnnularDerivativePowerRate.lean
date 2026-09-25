/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivativeLimits
import Erdos522.Probability.RealPowerConcentration
import Erdos522.Limits.SparseDegreeParameters

/-!
# Adjustable derivative and root-count powers

At derivative scale `L = N^ℓ` and count threshold `N^(1-d)`, the two mean
contributions have margins `4ℓ-d` and `1/2-2ℓ-d`. The mesh variance gives
failure `N^(-1/2+4ℓ+2d) (log N)^4`, with the same finite covariance and
local zero-count constants.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Erdos522

/-- The one-point jet bound after substitution of an arbitrary positive power scale. -/
theorem annularJetProbabilityBound_real_power_eq {N : ℕ} (hN : 1 < N)
    {S : ℝ} (hS : 0 < S) (C K ℓ : ℝ) :
    annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ ℓ)) (3 / (N : ℝ) ^ ℓ) =
      annularJetDensityCoefficient K S * (N : ℝ) ^ (-6 * ℓ) / Real.log N +
        jetGaussianErrorConstant C K * (N : ℝ) ^ (-1 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [annularJetProbabilityBound_eq hN hS (Real.rpow_pos_of_pos hn _) C K]
  have hL : ((N : ℝ) ^ ℓ) ^ 6 = (N : ℝ) ^ (6 * ℓ) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    ring
  rw [hL, Real.sqrt_eq_rpow, show -6 * ℓ = -(6 * ℓ) by ring,
    show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn.le, Real.rpow_neg hn.le]
  ring

/-- The normalized mean estimate displays its two exact power margins. -/
theorem annular_mean_real_power_identity {x c M a b ℓ d : ℝ} (hx : 0 < x) :
    (M * x * (x ^ ℓ) ^ 2 * Real.log x *
      (a * x ^ (-6 * ℓ) / Real.log x + b * x ^ (-1 / 2 : ℝ))) *
      (4 * c * Real.log x) / x ^ (1 - d) =
    4 * c * M * a * Real.log x / x ^ (4 * ℓ - d) +
      4 * c * M * b * (Real.log x) ^ 2 / x ^ (1 / 2 - 2 * ℓ - d) := by
  by_cases hlog : Real.log x = 0
  · simp [hlog]
  have hL : (x ^ ℓ) ^ 2 = x ^ (2 * ℓ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    ring
  have hp₁ : x * x ^ (2 * ℓ) * x ^ (-6 * ℓ) / x ^ (1 - d) = 1 / x ^ (4 * ℓ - d) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx,
      show 1 + 2 * ℓ + -6 * ℓ - (1 - d) = -(4 * ℓ - d) by ring, Real.rpow_neg hx.le]
    simp only [one_div]
  have hp₂ : x * x ^ (2 * ℓ) * x ^ (-1 / 2 : ℝ) / x ^ (1 - d) =
      1 / x ^ (1 / 2 - 2 * ℓ - d) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx,
      show 1 + 2 * ℓ + (-1 / 2 : ℝ) - (1 - d) = -(1 / 2 - 2 * ℓ - d) by ring,
      Real.rpow_neg hx.le]
    simp only [one_div]
  rw [hL]
  calc
    _ = 4 * c * M * a * Real.log x *
        (x * x ^ (2 * ℓ) * x ^ (-6 * ℓ) / x ^ (1 - d)) +
      4 * c * M * b * (Real.log x) ^ 2 *
        (x * x ^ (2 * ℓ) * x ^ (-1 / 2 : ℝ) / x ^ (1 - d)) := by field_simp
    _ = _ := by rw [hp₁, hp₂]; ring

/-- The mesh Chebyshev term retains its exact exponent at arbitrary scales. -/
theorem annular_mesh_real_power_identity {x c M v ℓ d : ℝ} (hx : 0 < x) :
    4 * (M * x * (x ^ ℓ) ^ 2 * Real.log x) ^ 2 * v /
      (Real.sqrt x * (x ^ (1 - d) / (2 * c * Real.log x)) ^ 2) =
      16 * c ^ 2 * v * M ^ 2 * x ^ (-1 / 2 + 4 * ℓ + 2 * d) * (Real.log x) ^ 4 := by
  have hL : (x ^ ℓ) ^ 4 = x ^ (4 * ℓ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    ring
  have hQ : (x ^ (1 - d)) ^ 2 = x ^ (2 * (1 - d)) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    ring
  have hp : x ^ 2 * x ^ (4 * ℓ) / (Real.sqrt x * x ^ (2 * (1 - d))) =
      x ^ (-1 / 2 + 4 * ℓ + 2 * d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_add hx,
      ← Real.rpow_add hx, ← Real.rpow_sub hx]
    congr 1
    ring
  calc
    _ = 16 * c ^ 2 * v * M ^ 2 *
        (x ^ 2 * (x ^ ℓ) ^ 4 / (Real.sqrt x * (x ^ (1 - d)) ^ 2)) * (Real.log x) ^ 4 := by
      ring_nf
      simp only [inv_inv]
      ring
    _ = _ := by rw [hL, hQ, hp]

/-- The one-point detection probability tends to zero at every positive derivative power. -/
theorem tendsto_annularJetProbabilityBound_real_power {S ℓ : ℝ}
    (hS : 0 < S) (hℓ : 0 < ℓ) (C K : ℝ) :
    Tendsto (fun N : ℕ => annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ ℓ)) (3 / (N : ℝ) ^ ℓ)) atTop (𝓝 0) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have h₁ := (tendsto_nat_rpow_neg (show 0 < 6 * ℓ by positivity)).mul hlog
  have h₂ := tendsto_nat_rpow_neg (by norm_num : (0 : ℝ) < 1 / 2)
  have ht : Tendsto (fun N : ℕ =>
      annularJetDensityCoefficient K S * (N : ℝ) ^ (-6 * ℓ) / Real.log N +
        jetGaussianErrorConstant C K * (N : ℝ) ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_def, Pi.inv_apply, neg_div, div_eq_mul_inv,
      neg_mul, mul_assoc] using (h₁.const_mul (annularJetDensityCoefficient K S)).add
        (h₂.const_mul (jetGaussianErrorConstant C K))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (annularJetProbabilityBound_real_power_eq (by omega : 1 < N) hS C K ℓ).symm

/-- The normalized mesh mean vanishes under its two strict power inequalities. -/
theorem tendsto_annular_mean_real_power_ratio {S ℓ d : ℝ} (hS : 0 < S)
    (hmean : d < 4 * ℓ) (hgauss : d < 1 / 2 - 2 * ℓ) (C K c : ℝ) :
    Tendsto (fun N : ℕ =>
      (annularMeshSizeConstant K S * N * ((N : ℝ) ^ ℓ) ^ 2 * Real.log N *
        annularJetProbabilityBound N C K (derivativeMeshValueThreshold N S ((N : ℝ) ^ ℓ))
          (3 / (N : ℝ) ^ ℓ)) * (4 * c * Real.log N) / (N : ℝ) ^ (1 - d)) atTop (𝓝 0) := by
  have h₁ := (tendsto_log_pow_div_nat_rpow 1 (show 0 < 4 * ℓ - d by linarith)).const_mul
    (4 * c * annularMeshSizeConstant K S * annularJetDensityCoefficient K S)
  have h₂ := (tendsto_log_pow_div_nat_rpow 2 (show 0 < 1 / 2 - 2 * ℓ - d by linarith)).const_mul
    (4 * c * annularMeshSizeConstant K S * jetGaussianErrorConstant C K)
  have ht := h₁.add h₂
  simp only [mul_zero, add_zero, pow_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [annularJetProbabilityBound_real_power_eq (by omega : 1 < N) hS C K ℓ]
  convert (annular_mean_real_power_identity (x := (N : ℝ))
    (by exact_mod_cast (show 0 < N by omega))).symm using 1
  ring

/-- The omitted angular sectors are negligible below every count power greater than `1/2`. -/
theorem tendsto_annular_sector_real_power_ratio {d : ℝ} (hd : d < 1 / 2) (c : ℝ) :
    Tendsto (fun N : ℕ => 80 * c * Real.log N * Real.sqrt N /
      (N : ℝ) ^ (1 - d)) atTop (𝓝 0) := by
  have ht := (tendsto_log_pow_div_nat_rpow 1 (show 0 < 1 / 2 - d by linarith)).const_mul (80 * c)
  simp only [mul_zero, pow_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : Real.sqrt N / (N : ℝ) ^ (1 - d) = 1 / (N : ℝ) ^ (1 / 2 - d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn,
      show (1 / 2 : ℝ) - (1 - d) = -(1 / 2 - d) by ring, Real.rpow_neg hn.le]
    simp only [one_div]
  rw [show 80 * c * Real.log N * Real.sqrt N / (N : ℝ) ^ (1 - d) =
      80 * c * Real.log N * (Real.sqrt N / (N : ℝ) ^ (1 - d)) by ring, hp]
  ring

/-- For fixed widths, the mean and sector thresholds in the quantitative root bound hold eventually. -/
theorem eventually_annular_derivative_power_scalar_bounds {K K' C ℓ d : ℝ}
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') (hC : 0 < C)
    (hℓ : 0 < ℓ) (hmean : d < 4 * ℓ) (hgauss : d < 1 / 2 - 2 * ℓ) (hd : d < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      annularJetProbabilityBound N C K
        (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))
          (3 / (N : ℝ) ^ ℓ) ≤ 1 ∧
      (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))) : ℝ) *
        annularJetProbabilityBound N C K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))
            (3 / (N : ℝ) ^ ℓ) ≤
        (N : ℝ) ^ (1 - d) / (4 * LocalZeroCount.localCountConstant K' * Real.log N) ∧
      40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (1 - d) / 2 := by
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant K'
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hSp : 0 < S := by linarith
  have hc : 0 < c := by
    have hK' : 0 ≤ K' := by linarith
    dsimp [c, LocalZeroCount.localCountConstant, ArcEnergy.arcScale]
    positivity
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_annularJetProbabilityBound_real_power hSp hℓ C K).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_mean_real_power_ratio hSp hmean hgauss C K c).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_annular_sector_real_power_ratio hd c).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
      with N hN hp hmean hsector
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have hpow : 0 < (N : ℝ) ^ (1 - d) := Real.rpow_pos_of_pos (by linarith) _
  have hL : 1 ≤ (N : ℝ) ^ ℓ := Real.one_le_rpow hn.le hℓ.le
  have hprob : 0 ≤ annularJetProbabilityBound N C K
      (derivativeMeshValueThreshold N S ((N : ℝ) ^ ℓ))
        (3 / (N : ℝ) ^ ℓ) := by
    unfold annularJetProbabilityBound
    have hG := jetGaussianErrorConstant_pos C K hC
    positivity
  refine ⟨hp.le, ?_, ?_⟩
  · have hcard := annular_mesh_cardinality_le (K := K) hN hK hS hL
    have hc' : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N S ((N : ℝ) ^ ℓ))) : ℝ) ≤
        annularMeshSizeConstant K S * N * ((N : ℝ) ^ ℓ) ^ 2 * Real.log N := by
      simpa only [annularMeshSizeConstant, mul_assoc] using hcard
    apply (mul_le_mul_of_nonneg_right hc' hprob).trans
    apply (le_div_iff₀ (show 0 < 4 * c * Real.log N by positivity)).mpr
    simpa only [one_mul] using ((div_lt_one hpow).mp hmean).le
  · have hsector' := (div_lt_one hpow).mp hsector
    dsimp [annularLocalMultiplicityBound]
    dsimp [c] at hsector'
    linarith


/-- The mesh tail has its exact polynomial failure rate at arbitrary power scales. -/
theorem annular_mesh_real_power_tail_rate_le {ℓ d : ℝ} {N : ℕ} (hN : 2 ≤ N) {K c C p M : ℝ}
    (_hK : 0 ≤ K) (hC : 0 < C) (hp : p ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ annularMeshSizeConstant K (annularDerivativeScale K) * N *
      ((N : ℝ) ^ ℓ) ^ 2 * Real.log N) :
    4 * M ^ 2 * (annularJetPairConstant C K + 5 * p) /
      (Real.sqrt N * ((N : ℝ) ^ (1 - d) / (2 * c * Real.log N)) ^ 2) ≤
      16 * c ^ 2 * (annularJetPairConstant C K + 5) *
        (annularMeshSizeConstant K (annularDerivativeScale K)) ^ 2 *
        (N : ℝ) ^ (-1 / 2 + 4 * ℓ + 2 * d) * (Real.log N) ^ 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : 0 ≤ annularJetPairConstant C K + 5 := by
    have hpos := annularJetPairConstant_pos C K hC
    linarith
  have hMsq := pow_le_pow_left₀ hM0 hM 2
  calc
    _ ≤ 4 * M ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (1 - d) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : annularJetPairConstant C K + 5 * p ≤
          annularJetPairConstant C K + 5) (by positivity)) (by positivity)
    _ ≤ 4 * (annularMeshSizeConstant K (annularDerivativeScale K) * N *
        ((N : ℝ) ^ ℓ) ^ 2 * Real.log N) ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (1 - d) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq (by norm_num)) hV) (by positivity)
    _ = _ := annular_mesh_real_power_identity hNr

/-- The finite annular count estimate retains its constants at arbitrary derivative and count powers. -/
theorem exists_annular_derivative_power_failure_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (ℓ d : ℝ) (_ : 0 ≤ ℓ) (N : ℕ) (_ : 2 ≤ N) (K K' : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : K + 1 ≤ (N : ℝ)) (_ : K + 2 ≤ K')
      (_ : ArcEnergy.arcScale * Real.log N / N ≤ 1)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : annularJetProbabilityBound N C₁ K
        (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))
          (3 / (N : ℝ) ^ ℓ) ≤ 1)
      (_ : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))) : ℝ) *
        annularJetProbabilityBound N C₁ K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ ℓ))
            (3 / (N : ℝ) ^ ℓ) ≤
        (N : ℝ) ^ (1 - d) / (4 * LocalZeroCount.localCountConstant K' * Real.log N))
      (_ : 40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (1 - d) / 2),
      (LogMoments.signMeasure N).real {ω | (N : ℝ) ^ (1 - d) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K
          ((N : ℝ) ^ ℓ) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
        annularSmallDerivativeFailureConstant C₂ K K' *
          (N : ℝ) ^ (-1 / 2 + 4 * ℓ + 2 * d) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_annular_small_derivative_constants
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro ℓ d hℓ N hN K K' hK hKN hKN' hKK' hwidth hdegree hp hmean hsector
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hNr
  have hK' : 0 ≤ K' := by linarith
  have hc : 0 < LocalZeroCount.localCountConstant K' := by
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  let L := (N : ℝ) ^ ℓ
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant K'
  let Q := (N : ℝ) ^ (1 - d) / (2 * c * Real.log N)
  have hL : 1 ≤ L := Real.one_le_rpow hNr.le hℓ
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hQ : 0 < Q := by dsimp [Q, c]; positivity
  have hmean' : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2 := by
    convert hmean using 1
    dsimp [Q, c]
    ring
  have hBQ : annularLocalMultiplicityBound N K' * Q = (N : ℝ) ^ (1 - d) / 2 := by
    dsimp [annularLocalMultiplicityBound, Q, c]
    field_simp
  have hthreshold : annularLocalMultiplicityBound N K' * Q +
      40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (1 - d) := by
    rw [hBQ]
    linarith
  have h := hprob N hN K K' L Q ((N : ℝ) ^ (1 - d)) hK hKN hKN' hKK' hL
    hwidth hdegree hQ hmean' hthreshold
  apply h.trans
  apply add_le_add_right
  have hM : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN hK hS hL
  exact annular_mesh_real_power_tail_rate_le hN hK hC₂ hp (Nat.cast_nonneg _) hM


/-- Fixed annular widths admit an unconditional eventual quantitative small-derivative estimate. -/
theorem eventually_annular_derivative_power_probability {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hmean : d < 4 * ℓ) (hgauss : d < 1 / 2 - 2 * ℓ) (hd : d < 1 / 2) (K K' : ℝ)
    (hK : 0 ≤ K) (hKK' : K + 2 ≤ K') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (LogMoments.signMeasure N).real {ω | (N : ℝ) ^ (1 - d) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K
          ((N : ℝ) ^ ℓ) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 + C *
        (N : ℝ) ^ (-1 / 2 + 4 * ℓ + 2 * d) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_annular_derivative_power_failure_constants
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
    eventually_annular_derivative_power_scalar_bounds hK hKK' hC₁ hℓ hmean hgauss hd]
      with N hN hKN hKN' hdegree hwidthN hscalar
  exact hprob ℓ d hℓ.le N hN K K' hK hKN hKN' hKK' hwidthN.le hdegree hscalar.1 hscalar.2.1 hscalar.2.2


/-- The full finite-degree exceptional probability is summable for every
admissible tuple of sparse-degree scales. -/
theorem summable_admissible_annular_derivative_failures {q t ℓ d κ : ℝ}
    (h : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun j : ℕ => (LogMoments.signMeasure (realPowerDegree q j)).real {ω |
      (realPowerDegree q j : ℝ) ^ (1 - d) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial (realPowerDegree q j) ω)
          (realPowerDegree q j) K ((realPowerDegree q j : ℝ) ^ ℓ) : ℝ)}) := by
  have hq2 : 2 < q := two_lt_of_occupation_summability hq h.logarithmic_pos h.occupation_summability
  obtain ⟨C, _, hbound⟩ := eventually_annular_derivative_power_probability h.derivative_pos
    h.mean_density h.mean_gaussian_error h.excluded_sectors K (K + 2) hK le_rfl
  have h₁ := summable_realPowerDegree_rpow hq (show q * (-3 : ℝ) < -1 by linarith)
  have h₂ := summable_realPowerDegree_rpow hq (show q * (-10 : ℝ) < -1 by linarith)
  have h₃ := ((h.summable_second_moment_envelopes hq 4).2.2).mul_left C
  have hsum : Summable (fun j : ℕ => 1 / (realPowerDegree q j : ℝ) ^ 3 +
      1 / (realPowerDegree q j : ℝ) ^ 10 + C *
        (realPowerDegree q j : ℝ) ^ (-1 / 2 + 4 * ℓ + 2 * d) *
          (Real.log (realPowerDegree q j)) ^ 4) := by
    apply (h₁.add h₂ |>.add h₃).congr
    intro j
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num only [Real.rpow_ofNat]
    ring
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_realPowerDegree hq).eventually hbound] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact hj

/-- Almost-sure annular derivative nondegeneracy with retuned powers, for
prefixes of the actual infinite sign sequence. -/
theorem ae_eventually_admissible_annular_derivative_count {q t ℓ d κ : ℝ}
    (h : AdmissibleSparseDegreeScales q t ℓ d κ) (hq : 0 < q) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂rademacherSequenceMeasure, ∀ᶠ j : ℕ in atTop,
      (annularSmallDerivativeZeroCount
        (rademacherPolynomial (realPowerDegree q j) (rademacherPrefix (realPowerDegree q j) ω))
          (realPowerDegree q j) K ((realPowerDegree q j : ℝ) ^ ℓ) : ℝ) ≤
            (realPowerDegree q j : ℝ) ^ (1 - d) := by
  have hbc := ae_eventually_rademacherPrefix_notMem (realPowerDegree q)
    (fun N => {v | (N : ℝ) ^ (1 - d) <
      (annularSmallDerivativeZeroCount (rademacherPolynomial N v) N K ((N : ℝ) ^ ℓ) : ℝ)})
    (summable_admissible_annular_derivative_failures h hq K hK)
  filter_upwards [hbc] with ω hω
  exact hω.mono (fun _ hj => le_of_not_gt hj)

end Erdos522

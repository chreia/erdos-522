/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AnnularSmallDerivative

/-!
# A polynomial failure rate for annular small derivatives

The derivative threshold `L = N^(1/64)` and count threshold
`N^(31/32)` make the mesh Chebyshev term proportional to
`N^(-3/8) (log N)^4`. The constants retain the actual Gaussian
approximation and local zero-count normalizations.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- The cardinality coefficient of the annular detection mesh. -/
def annularMeshSizeConstant (K S : ℝ) : ℝ := 2 ^ 18 * (K + 1) * S ^ 2

/-- The failure coefficient after specializing the mesh parameters. -/
def annularSmallDerivativeFailureConstant (C K K' : ℝ) : ℝ :=
  16 * (LocalZeroCount.localCountConstant K') ^ 2 * (annularJetPairConstant C K + 5) *
    (annularMeshSizeConstant K (annularDerivativeScale K)) ^ 2

/-- The power balance in the mesh-count Chebyshev estimate. -/
theorem annular_mesh_rate_identity {x c d v : ℝ} (hx : 0 < x) :
    4 * (d * x * (x ^ (1 / 64 : ℝ)) ^ 2 * Real.log x) ^ 2 * v /
      (Real.sqrt x * (x ^ (31 / 32 : ℝ) / (2 * c * Real.log x)) ^ 2) =
      16 * c ^ 2 * v * d ^ 2 * x ^ (-3 / 8 : ℝ) * (Real.log x) ^ 4 := by
  have hL : (x ^ (1 / 64 : ℝ)) ^ 4 = x ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  have hQ : (x ^ (31 / 32 : ℝ)) ^ 2 = x ^ (31 / 16 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  have hpower : x ^ 2 * x ^ (1 / 16 : ℝ) /
      (Real.sqrt x * x ^ (31 / 16 : ℝ)) = x ^ (-3 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_add hx,
      ← Real.rpow_add hx, ← Real.rpow_sub hx]
    congr 1
    norm_num
  calc
    _ = 16 * c ^ 2 * v * d ^ 2 *
        (x ^ 2 * (x ^ (1 / 64 : ℝ)) ^ 4 /
          (Real.sqrt x * (x ^ (31 / 32 : ℝ)) ^ 2)) * (Real.log x) ^ 4 := by
      ring_nf
      simp only [inv_inv]
      ring
    _ = _ := by rw [hL, hQ, hpower]

/-- The specialized mesh tail has the stated polynomial failure rate. -/
theorem annular_mesh_tail_rate_le {N : ℕ} (hN : 2 ≤ N) {K c C p M : ℝ}
    (_hK : 0 ≤ K) (hC : 0 < C) (hp : p ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ annularMeshSizeConstant K (annularDerivativeScale K) * N *
      ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N) :
    4 * M ^ 2 * (annularJetPairConstant C K + 5 * p) /
      (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) ≤
      16 * c ^ 2 * (annularJetPairConstant C K + 5) *
        (annularMeshSizeConstant K (annularDerivativeScale K)) ^ 2 *
        (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : 0 ≤ annularJetPairConstant C K + 5 := by
    have hpos := annularJetPairConstant_pos C K hC
    linarith
  have hMsq := pow_le_pow_left₀ hM0 hM 2
  calc
    _ ≤ 4 * M ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : annularJetPairConstant C K + 5 * p ≤
          annularJetPairConstant C K + 5) (by positivity)) (by positivity)
    _ ≤ 4 * (annularMeshSizeConstant K (annularDerivativeScale K) * N *
        ((N : ℝ) ^ (1 / 64 : ℝ)) ^ 2 * Real.log N) ^ 2 * (annularJetPairConstant C K + 5) /
        (Real.sqrt N * ((N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq (by norm_num)) hV) (by positivity)
    _ = _ := annular_mesh_rate_identity hNr

/-- The actual annular small-derivative count has failure `N⁻³ + N⁻¹⁰ + C N⁻³/⁸(log N)⁴`. -/
theorem exists_annular_small_derivative_failure_constants :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (N : ℕ) (_ : 2 ≤ N) (K K' : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N) (_ : K + 1 ≤ (N : ℝ)) (_ : K + 2 ≤ K')
      (_ : ArcEnergy.arcScale * Real.log N / N ≤ 1)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : annularJetProbabilityBound N C₁ K
        (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
          (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤ 1)
      (_ : (Fintype.card (AnnularMeshIndex N K
        (derivativeMeshSpacing N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))) : ℝ) *
        annularJetProbabilityBound N C₁ K
          (derivativeMeshValueThreshold N (annularDerivativeScale K) ((N : ℝ) ^ (1 / 64 : ℝ)))
            (3 / (N : ℝ) ^ (1 / 64 : ℝ)) ≤
        (N : ℝ) ^ (31 / 32 : ℝ) / (4 * LocalZeroCount.localCountConstant K' * Real.log N))
      (_ : 40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) / 2),
      (LogMoments.signMeasure N).real {ω | (N : ℝ) ^ (31 / 32 : ℝ) <
        (annularSmallDerivativeZeroCount (rademacherPolynomial N ω) N K
          ((N : ℝ) ^ (1 / 64 : ℝ)) : ℝ)} ≤
      1 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 10 +
        annularSmallDerivativeFailureConstant C₂ K K' *
          (N : ℝ) ^ (-3 / 8 : ℝ) * (Real.log N) ^ 4 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hprob⟩ := exists_annular_small_derivative_constants
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro N hN K K' hK hKN hKN' hKK' hwidth hdegree hp hmean hsector
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hNr
  have hK' : 0 ≤ K' := by linarith
  have hc : 0 < LocalZeroCount.localCountConstant K' := by
    unfold LocalZeroCount.localCountConstant ArcEnergy.arcScale
    positivity
  let L := (N : ℝ) ^ (1 / 64 : ℝ)
  let S := annularDerivativeScale K
  let c := LocalZeroCount.localCountConstant K'
  let Q := (N : ℝ) ^ (31 / 32 : ℝ) / (2 * c * Real.log N)
  have hL : 1 ≤ L := Real.one_le_rpow hNr.le (by norm_num)
  have hS : 1 ≤ S := one_le_annularDerivativeScale hK
  have hQ : 0 < Q := by dsimp [Q, c]; positivity
  have hmean' : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) *
      annularJetProbabilityBound N C₁ K (derivativeMeshValueThreshold N S L) (3 / L) ≤ Q / 2 := by
    convert hmean using 1
    dsimp [Q, c]
    ring
  have hBQ : annularLocalMultiplicityBound N K' * Q = (N : ℝ) ^ (31 / 32 : ℝ) / 2 := by
    dsimp [annularLocalMultiplicityBound, Q, c]
    field_simp
  have hthreshold : annularLocalMultiplicityBound N K' * Q +
      40 * annularLocalMultiplicityBound N K' * Real.sqrt N ≤ (N : ℝ) ^ (31 / 32 : ℝ) := by
    rw [hBQ]
    linarith
  have h := hprob N hN K K' L Q ((N : ℝ) ^ (31 / 32 : ℝ)) hK hKN hKN' hKK' hL
    hwidth hdegree hQ hmean' hthreshold
  apply h.trans
  apply add_le_add_right
  have hM : (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      annularMeshSizeConstant K S * N * L ^ 2 * Real.log N := by
    simpa only [annularMeshSizeConstant, mul_assoc] using annular_mesh_cardinality_le hN hK hS hL
  exact annular_mesh_tail_rate_le hN hK hC₂ hp (Nat.cast_nonneg _) hM

end Erdos522

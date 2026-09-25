/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ArcEnergy

/-!
# Real angular Gram matrices

A finite continuous family with an upper frame bound gives a positive
contractive Gram matrix on every measurable angular set. Its trace controls
the lower-tail probability of its energy under independent unit-proxy
sub-Gaussian coordinates.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators NNReal
namespace Erdos522.AngularGram
open ArcEnergy (Angle angularMeasure)

/-- A finite Fourier sum with real coordinates. -/
def finiteSum {n : ℕ} (v : Fin n → Angle → ℂ) (x : Fin n → ℝ)
    (θ : Angle) : ℂ := ∑ k, x k • (v k θ)

/-- Angular energy with fixed complex amplitudes. -/
def energy {n : ℕ} (v : Fin n → Angle → ℂ) (s : Set Angle)
    (x : Fin n → ℝ) : ℝ := ∫ θ in s, ‖finiteSum v x θ‖ ^ 2 ∂angularMeasure

/-- The real Gram matrix of the continuous complex functions on an angular set. -/
def gramMatrix {n : ℕ} (v : Fin n → Angle → ℂ) (s : Set Angle) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  ∫ θ in s, inner ℝ (v i θ) (v j θ) ∂angularMeasure

lemma continuous_finiteSum {n : ℕ}
    (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (x : Fin n → ℝ) :
    Continuous (finiteSum v x) := by
  unfold finiteSum
  apply continuous_finsetSum
  intro i _
  exact (continuous_const : Continuous (fun _ : Angle => x i)).smul (hv i)

lemma integrable_norm_sq_finiteSum {n : ℕ}
    (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (x : Fin n → ℝ) :
    Integrable (fun θ => ‖finiteSum v x θ‖ ^ 2) angularMeasure :=
  ((continuous_finiteSum v hv x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_basis {n : ℕ}
    (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (i j : Fin n) :
    Integrable (fun θ => inner ℝ (v i θ) (v j θ)) angularMeasure :=
  ((hv i).inner (hv j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma norm_sq_finiteSum {n : ℕ} (v : Fin n → Angle → ℂ)
    (x : Fin n → ℝ) (θ : Angle) :
    ‖finiteSum v x θ‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (v i θ) (v j θ) * x i * x j := by
  rw [← real_inner_self_eq_norm_sq, finiteSum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

theorem quadraticForm_gramMatrix {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i))
    (s : Set Angle) (x : Fin n → ℝ) :
    HansonWright.quadraticForm (gramMatrix v s) x = energy v s x := by
  unfold HansonWright.quadraticForm gramMatrix energy
  simp_rw [norm_sq_finiteSum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_mul_const]
    · intro j _
      exact (((integrable_inner_basis v hv i j).restrict).mul_const _).mul_const _
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      (((integrable_inner_basis v hv i j).restrict).mul_const _).mul_const _)

lemma gramMatrix_isHermitian {n : ℕ} (v : Fin n → Angle → ℂ) (s : Set Angle) :
    (gramMatrix v s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, gramMatrix]
  congr 1
  ext θ
  exact real_inner_comm _ _

lemma energy_nonneg {n : ℕ} (v : Fin n → Angle → ℂ) (s : Set Angle)
    (x : Fin n → ℝ) : 0 ≤ energy v s x :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem trace_gramMatrix {n : ℕ}
    (v : Fin n → Angle → ℂ) (s : Set Angle) :
    (gramMatrix v s).trace = ∑ i, ∫ θ in s, ‖v i θ‖ ^ 2 ∂angularMeasure := by
  simp only [Matrix.trace, Matrix.diag, gramMatrix, real_inner_self_eq_norm_sq]

/-- Restricting an angular integral preserves a full-circle upper frame bound. -/
theorem energy_le_sum_sq {n : ℕ}
    (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i))
    (hframe : ∀ x, energy v Set.univ x ≤ ∑ i, (x i) ^ 2)
    (s : Set Angle) (x : Fin n → ℝ) : energy v s x ≤ ∑ i, (x i) ^ 2 := by
  calc
    _ ≤ energy v Set.univ x := by
      unfold energy
      rw [Measure.restrict_univ]
      exact integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun _ => sq_nonneg _)) (integrable_norm_sq_finiteSum v hv x)
    _ ≤ _ := hframe x

lemma dotProduct_gramMatrix {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (s : Set Angle)
    (x : Fin n → ℝ) :
    star x ⬝ᵥ ((gramMatrix v s) *ᵥ x) = energy v s x := by
  rw [← quadraticForm_gramMatrix v hv]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, HansonWright.quadraticForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gramMatrix_posSemidef {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (s : Set Angle) :
    (gramMatrix v s).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gramMatrix_isHermitian v s)
  intro x
  rw [dotProduct_gramMatrix v hv]
  exact energy_nonneg v s x

open scoped MatrixOrder Matrix.Norms.L2Operator

theorem gramMatrix_le_one {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i))
    (hframe : ∀ x, energy v Set.univ x ≤ ∑ i, (x i) ^ 2) (s : Set Angle) : gramMatrix v s ≤ 1 := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (gramMatrix_isHermitian v s))
  intro x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_gramMatrix v hv]
  have h := energy_le_sum_sq v hv hframe s x
  simpa [dotProduct, pow_two] using sub_nonneg.mpr h

theorem operatorNorm_gramMatrix_le_one {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i))
    (hframe : ∀ x, energy v Set.univ x ≤ ∑ i, (x i) ^ 2) (s : Set Angle) :
    HansonWright.operatorNorm (gramMatrix v s) ≤ 1 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (gramMatrix v s)
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (gramMatrix_isHermitian v s)
  change ‖T‖ ≤ 1
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  have heq : inner ℝ (T x) x = energy v s (fun i => x i) := by
    rw [← quadraticForm_gramMatrix v hv, HansonWright.quadraticForm_eq_inner_toEuclideanCLM]
  have hn : (∑ i, (x i) ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  have hnonneg := energy_nonneg v s (fun i => x i)
  have hle := energy_le_sum_sq v hv hframe s (fun i => x i)
  rw [hn] at hle
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, heq,
    abs_of_nonneg (div_nonneg hnonneg (sq_nonneg _))]
  by_cases hx : x = 0
  · simp [hx]
  · exact (div_le_one₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr hle

theorem frobeniusNormSq_gramMatrix_le_trace {n : ℕ} (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i))
    (hframe : ∀ x, energy v Set.univ x ≤ ∑ i, (x i) ^ 2) (s : Set Angle) :
    HansonWright.frobeniusNormSq (gramMatrix v s) ≤ (gramMatrix v s).trace := by
  have hc : Commute (gramMatrix v s) (1 - gramMatrix v s) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have hpos := hc.mul_nonneg (gramMatrix_posSemidef v hv s).nonneg
    (sub_nonneg.mpr (gramMatrix_le_one v hv hframe s))
  have hsq : gramMatrix v s * gramMatrix v s ≤ gramMatrix v s := by
    simpa only [mul_sub, mul_one, sub_nonneg] using hpos
  have h := (Matrix.le_iff.mp hsq).trace_nonneg
  rw [Matrix.trace_sub] at h
  have heq : (gramMatrix v s * gramMatrix v s).trace =
      HansonWright.frobeniusNormSq (gramMatrix v s) := by
    calc
      _ = ((gramMatrix v s).conjTranspose * gramMatrix v s).trace := by
        rw [(gramMatrix_isHermitian v s).eq]
      _ = _ := HansonWright.matrix_trace_conjTranspose_mul_self_eq_frobeniusNormSq _
  rw [heq] at h
  linarith

/-- Positive trace makes both matrix norms strictly positive. -/
lemma gramMatrix_norms_pos {n : ℕ} (v : Fin n → Angle → ℂ) (s : Set Angle)
    (htrace : 0 < (gramMatrix v s).trace) :
    0 < HansonWright.frobeniusNorm (gramMatrix v s) ∧
      0 < HansonWright.operatorNorm (gramMatrix v s) := by
  have hne : gramMatrix v s ≠ 0 := by
    intro h
    simp [h] at htrace
  have hij : ∃ i j, gramMatrix v s i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Matrix.ext h)
  obtain ⟨i, j, hij⟩ := hij
  constructor
  · apply Real.sqrt_pos.mpr
    unfold HansonWright.frobeniusNormSq
    apply Finset.sum_pos'
    · intro _ _
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
      exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hij⟩
  · apply norm_pos_iff.mpr
    intro h
    exact hne (Matrix.toEuclideanCLM.injective (by simpa using h))

/-- The centered arc-energy inequality applies to a finite continuous family
with unit upper frame bound. -/
theorem centered_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (v : Fin n → Angle → ℂ) (hv : ∀ i, Continuous (v i)) (hframe : ∀ x, energy v Set.univ x ≤ ∑ i, (x i) ^ 2) (s : Set Angle)
    (htrace : 0 < (gramMatrix v s).trace)
    (X : Fin n → Ω → ℝ) (hind : ProbabilityTheory.iIndepFun X μ)
    (hsub : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) 1 μ) :
    μ.real {ω | (gramMatrix v s).trace / 2 ≤
      |HansonWright.centeredQuadraticForm μ (gramMatrix v s) X ω|} ≤
        2 * Real.exp (-(gramMatrix v s).trace / 16384) := by
  let T := (gramMatrix v s).trace
  obtain ⟨hF, hO⟩ := gramMatrix_norms_pos v s htrace
  have hFsq := frobeniusNormSq_gramMatrix_le_trace v hv hframe s
  rw [← HansonWright.frobeniusNorm_sq] at hFsq
  have hO1 := operatorNorm_gramMatrix_le_one v hv hframe s
  have he0 := Real.exp_pos 1
  have he1 := Real.exp_one_lt_three
  have he2 : Real.exp 1 ^ 2 < (3 : ℝ) ^ 2 := pow_lt_pow_left₀ he1 he0.le (by decide)
  have he3 : Real.exp 1 ^ 3 < (3 : ℝ) ^ 3 := pow_lt_pow_left₀ he1 he0.le (by decide)
  have h := HansonWright.hanson_wright_inequality (A := gramMatrix v s) (X := X)
    (K := 1) (C := 1024) (t := T / 2)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by nlinarith) (by nlinarith)
    hF hO hind (by
      have hproxy : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : ℝ≥0) = 1 := by ext; norm_num
      intro i
      rw [hproxy]
      exact hsub i) (by dsimp [T]; positivity)
  simp only [one_pow, one_mul] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hfirst : T / 4 ≤ (T / 2) ^ 2 / HansonWright.frobeniusNorm (gramMatrix v s) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hF)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hFsq htrace.le]
  have hsecond : T / 4 ≤ T / 2 / HansonWright.operatorNorm (gramMatrix v s) := by
    apply (le_div_iff₀ hO).mpr
    nlinarith [mul_le_mul_of_nonneg_left hO1 htrace.le]
  have hm := le_min hfirst hsecond
  dsimp [T] at *
  linarith


end Erdos522.AngularGram

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.ArcEnergy

/-!
# Arc energy with fixed complex amplitudes

The real Gram matrix of complex Fourier monomials is a positive contraction
when the amplitudes have modulus at most one. Independent signs then give an
arc-energy lower tail with exponent proportional to the Gram trace. The
amplitudes may have arbitrary phases and may vanish.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators NNReal
namespace Erdos522.ArcEnergy

/-- A complex-amplitude Fourier sum with real coordinates. -/
def weightedFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ) (x : Fin (N + 1) → ℝ)
    (θ : Angle) : ℂ := ∑ k, x k • (a k * fourier (k : ℤ) θ)

/-- Angular energy with fixed complex amplitudes. -/
def weightedEnergy {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (x : Fin (N + 1) → ℝ) : ℝ := ∫ θ in s, ‖weightedFourierSum a x θ‖ ^ 2 ∂angularMeasure

/-- The real Gram matrix of the complex-amplitude monomials on an angular set. -/
def weightedGramMatrix {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun i j =>
  ∫ θ in s, inner ℝ (a i * fourier (i : ℤ) θ) (a j * fourier (j : ℤ) θ) ∂angularMeasure

lemma continuous_weightedFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (x : Fin (N + 1) → ℝ) : Continuous (weightedFourierSum a x) := by
  unfold weightedFourierSum
  fun_prop

lemma integrable_norm_sq_weightedFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (x : Fin (N + 1) → ℝ) :
    Integrable (fun θ => ‖weightedFourierSum a x θ‖ ^ 2) angularMeasure :=
  ((continuous_weightedFourierSum a x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_weighted_fourier {N : ℕ} (a : Fin (N + 1) → ℂ)
    (i j : Fin (N + 1)) :
    Integrable (fun θ : Angle => inner ℝ (a i * fourier (i : ℤ) θ)
      (a j * fourier (j : ℤ) θ)) angularMeasure :=
  (((fourier (i : ℤ)).continuous.const_mul _).inner
    ((fourier (j : ℤ)).continuous.const_mul _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma norm_sq_weightedFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ)
    (x : Fin (N + 1) → ℝ) (θ : Angle) :
    ‖weightedFourierSum a x θ‖ ^ 2 = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      inner ℝ (a i * fourier (i : ℤ) θ) (a j * fourier (j : ℤ) θ) * x i * x j := by
  rw [← real_inner_self_eq_norm_sq, weightedFourierSum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

theorem quadraticForm_weightedGramMatrix {N : ℕ} (a : Fin (N + 1) → ℂ)
    (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    HansonWright.quadraticForm (weightedGramMatrix a s) x = weightedEnergy a s x := by
  unfold HansonWright.quadraticForm weightedGramMatrix weightedEnergy
  simp_rw [norm_sq_weightedFourierSum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_mul_const]
    · intro j _
      exact (((integrable_inner_weighted_fourier a i j).restrict).mul_const _).mul_const _
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      (((integrable_inner_weighted_fourier a i j).restrict).mul_const _).mul_const _)

lemma weightedGramMatrix_isHermitian {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) :
    (weightedGramMatrix a s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, weightedGramMatrix]
  congr 1
  ext θ
  exact real_inner_comm _ _

lemma weightedEnergy_nonneg {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (x : Fin (N + 1) → ℝ) : 0 ≤ weightedEnergy a s x :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma weightedGramMatrix_diagonal {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (i : Fin (N + 1)) :
    weightedGramMatrix a s i i = ‖a i‖ ^ 2 * angularMeasure.real s := by
  simp only [weightedGramMatrix, real_inner_self_eq_norm_sq, norm_mul, fourier_apply,
    Circle.norm_coe, mul_one, integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply_univ]
  ring

theorem trace_weightedGramMatrix {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) :
    (weightedGramMatrix a s).trace = (∑ k, ‖a k‖ ^ 2) * angularMeasure.real s := by
  simp only [Matrix.trace, Matrix.diag, weightedGramMatrix_diagonal, Finset.sum_mul]

/-- Parseval retains the amplitude weights exactly. -/
theorem weightedEnergy_univ {N : ℕ} (a : Fin (N + 1) → ℂ) (x : Fin (N + 1) → ℝ) :
    weightedEnergy a Set.univ x = ∑ k, ‖a k‖ ^ 2 * (x k) ^ 2 := by
  have heq : weightedFourierSum a x = LogMoments.fourierPolynomial
      (fun k => (x k : ℂ) * a k) (fun _ => true) := by
    ext θ
    simp [weightedFourierSum, LogMoments.fourierPolynomial_eq_sum, LogMoments.sign,
      Algebra.smul_def, mul_assoc]
  simp only [weightedEnergy, Measure.restrict_univ, heq,
    LogMoments.integral_norm_sq_fourierPolynomial, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weightedEnergy_le_sum_sq {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    weightedEnergy a s x ≤ ∑ k, (x k) ^ 2 := by
  calc
    _ ≤ weightedEnergy a Set.univ x := by
      unfold weightedEnergy
      rw [Measure.restrict_univ]
      exact integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun _ => sq_nonneg _)) (integrable_norm_sq_weightedFourierSum a x)
    _ = ∑ k, ‖a k‖ ^ 2 * (x k) ^ 2 := weightedEnergy_univ a x
    _ ≤ _ := Finset.sum_le_sum fun k _ => by
      have hk := pow_le_pow_left₀ (norm_nonneg _) (ha k) 2
      simpa using mul_le_mul_of_nonneg_right hk (sq_nonneg (x k))

lemma dotProduct_weightedGramMatrix {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (x : Fin (N + 1) → ℝ) :
    star x ⬝ᵥ ((weightedGramMatrix a s) *ᵥ x) = weightedEnergy a s x := by
  rw [← quadraticForm_weightedGramMatrix]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, HansonWright.quadraticForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightedGramMatrix_posSemidef {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) :
    (weightedGramMatrix a s).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (weightedGramMatrix_isHermitian a s)
  intro x
  rw [dotProduct_weightedGramMatrix]
  exact weightedEnergy_nonneg a s x

open scoped MatrixOrder Matrix.Norms.L2Operator

theorem weightedGramMatrix_le_one {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle) : weightedGramMatrix a s ≤ 1 := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (weightedGramMatrix_isHermitian a s))
  intro x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_weightedGramMatrix]
  have h := weightedEnergy_le_sum_sq a ha s x
  simpa [dotProduct, pow_two] using sub_nonneg.mpr h

theorem operatorNorm_weightedGramMatrix_le_one {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle) :
    HansonWright.operatorNorm (weightedGramMatrix a s) ≤ 1 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedGramMatrix a s)
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (weightedGramMatrix_isHermitian a s)
  change ‖T‖ ≤ 1
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  have heq : inner ℝ (T x) x = weightedEnergy a s (fun i => x i) := by
    rw [← quadraticForm_weightedGramMatrix, HansonWright.quadraticForm_eq_inner_toEuclideanCLM]
  have hn : (∑ i, (x i) ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  have hnonneg := weightedEnergy_nonneg a s (fun i => x i)
  have hle := weightedEnergy_le_sum_sq a ha s (fun i => x i)
  rw [hn] at hle
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, heq,
    abs_of_nonneg (div_nonneg hnonneg (sq_nonneg _))]
  by_cases hx : x = 0
  · simp [hx]
  · exact (div_le_one₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr hle

theorem frobeniusNormSq_weightedGramMatrix_le_trace {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle) :
    HansonWright.frobeniusNormSq (weightedGramMatrix a s) ≤ (weightedGramMatrix a s).trace := by
  have hc : Commute (weightedGramMatrix a s) (1 - weightedGramMatrix a s) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have hpos := hc.mul_nonneg (weightedGramMatrix_posSemidef a s).nonneg
    (sub_nonneg.mpr (weightedGramMatrix_le_one a ha s))
  have hsq : weightedGramMatrix a s * weightedGramMatrix a s ≤ weightedGramMatrix a s := by
    simpa only [mul_sub, mul_one, sub_nonneg] using hpos
  have h := (Matrix.le_iff.mp hsq).trace_nonneg
  rw [Matrix.trace_sub] at h
  have heq : (weightedGramMatrix a s * weightedGramMatrix a s).trace =
      HansonWright.frobeniusNormSq (weightedGramMatrix a s) := by
    calc
      _ = ((weightedGramMatrix a s).conjTranspose * weightedGramMatrix a s).trace := by
        rw [(weightedGramMatrix_isHermitian a s).eq]
      _ = _ := HansonWright.matrix_trace_conjTranspose_mul_self_eq_frobeniusNormSq _
  rw [heq] at h
  linarith

/-- Positive trace makes both matrix norms strictly positive. -/
lemma weightedGramMatrix_norms_pos {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (htrace : 0 < (weightedGramMatrix a s).trace) :
    0 < HansonWright.frobeniusNorm (weightedGramMatrix a s) ∧
      0 < HansonWright.operatorNorm (weightedGramMatrix a s) := by
  have hne : weightedGramMatrix a s ≠ 0 := by
    intro h
    simp [h] at htrace
  have hij : ∃ i j, weightedGramMatrix a s i j ≠ 0 := by
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

/-- The centered arc-energy inequality applies to arbitrary fixed complex
amplitudes bounded by one. -/
theorem centered_weighted_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle)
    (htrace : 0 < (weightedGramMatrix a s).trace)
    (X : Fin (N + 1) → Ω → ℝ) (hind : ProbabilityTheory.iIndepFun X μ)
    (hsub : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) 1 μ) :
    μ.real {ω | (weightedGramMatrix a s).trace / 2 ≤
      |HansonWright.centeredQuadraticForm μ (weightedGramMatrix a s) X ω|} ≤
        2 * Real.exp (-(weightedGramMatrix a s).trace / 16384) := by
  let T := (weightedGramMatrix a s).trace
  obtain ⟨hF, hO⟩ := weightedGramMatrix_norms_pos a s htrace
  have hFsq := frobeniusNormSq_weightedGramMatrix_le_trace a ha s
  rw [← HansonWright.frobeniusNorm_sq] at hFsq
  have hO1 := operatorNorm_weightedGramMatrix_le_one a ha s
  have he0 := Real.exp_pos 1
  have he1 := Real.exp_one_lt_three
  have he2 : Real.exp 1 ^ 2 < (3 : ℝ) ^ 2 := pow_lt_pow_left₀ he1 he0.le (by decide)
  have he3 : Real.exp 1 ^ 3 < (3 : ℝ) ^ 3 := pow_lt_pow_left₀ he1 he0.le (by decide)
  have h := HansonWright.hanson_wright_inequality (A := weightedGramMatrix a s) (X := X)
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
  have hfirst : T / 4 ≤ (T / 2) ^ 2 / HansonWright.frobeniusNorm (weightedGramMatrix a s) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hF)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hFsq htrace.le]
  have hsecond : T / 4 ≤ T / 2 / HansonWright.operatorNorm (weightedGramMatrix a s) := by
    apply (le_div_iff₀ hO).mpr
    nlinarith [mul_le_mul_of_nonneg_left hO1 htrace.le]
  have hm := le_min hfirst hsecond
  dsimp [T] at *
  linarith

/-- Arc energy under independent signs and fixed complex amplitudes. -/
def weightedRandomEnergy {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle)
    (ω : LogMoments.SignVector N) : ℝ := weightedEnergy a s (fun i => LogMoments.realSign (ω i))

lemma weightedRandomEnergy_eq_quadraticForm {N : ℕ} (a : Fin (N + 1) → ℂ)
    (s : Set Angle) (ω : LogMoments.SignVector N) :
    weightedRandomEnergy a s ω = HansonWright.randomQuadraticForm (weightedGramMatrix a s)
      (fun i ω => LogMoments.realSign (ω i)) ω :=
  (quadraticForm_weightedGramMatrix a s (fun i => LogMoments.realSign (ω i))).symm

theorem integral_weightedRandomEnergy {N : ℕ} (a : Fin (N + 1) → ℂ) (s : Set Angle) :
    (∫ ω, weightedRandomEnergy a s ω ∂LogMoments.signMeasure N) = (weightedGramMatrix a s).trace := by
  simp_rw [weightedRandomEnergy_eq_quadraticForm, HansonWright.randomQuadraticForm,
    HansonWright.quadraticForm]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [mul_assoc, integral_const_mul, LogMoments.integral_mul_realSign_coordinates]
  simp

/-- Complex phases and zero amplitudes preserve the unit-proxy lower-tail
estimate, with their energy appearing exactly in the trace. -/
theorem weightedRandomEnergy_lower_tail {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ha : ∀ k, ‖a k‖ ≤ 1) (s : Set Angle) (hs : 0 < angularMeasure.real s)
    (henergy : 0 < ∑ k, ‖a k‖ ^ 2) :
    (LogMoments.signMeasure N).real
      {ω | weightedRandomEnergy a s ω ≤ (∑ k, ‖a k‖ ^ 2) * angularMeasure.real s / 2} ≤
        2 * Real.exp (-((∑ k, ‖a k‖ ^ 2) * angularMeasure.real s) / 16384) := by
  rw [← trace_weightedGramMatrix]
  have htrace : 0 < (weightedGramMatrix a s).trace := by
    rw [trace_weightedGramMatrix]
    positivity
  have htail := centered_weighted_energy_tail a ha s htrace
    (fun i (ω : LogMoments.SignVector N) => LogMoments.realSign (ω i))
    (LogMoments.iIndepFun_realSign N) LogMoments.hasSubgaussianMGF_coordinate
  refine (measureReal_mono (fun ω hω => ?_)).trans htail
  change (weightedGramMatrix a s).trace / 2 ≤
    |HansonWright.centeredQuadraticForm (LogMoments.signMeasure N)
      (weightedGramMatrix a s) (fun i ω => LogMoments.realSign (ω i)) ω|
  simp only [HansonWright.centeredQuadraticForm, ← weightedRandomEnergy_eq_quadraticForm,
    integral_weightedRandomEnergy]
  have hneg := neg_le_abs (weightedRandomEnergy a s ω - (weightedGramMatrix a s).trace)
  change weightedRandomEnergy a s ω ≤ (weightedGramMatrix a s).trace / 2 at hω
  linarith

theorem weightedFourierSum_const_mul {N : ℕ} (c : ℂ) (a : Fin (N + 1) → ℂ)
    (x : Fin (N + 1) → ℝ) (θ : Angle) :
    weightedFourierSum (fun k => c * a k) x θ = c * weightedFourierSum a x θ := by
  simp only [weightedFourierSum, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weightedRandomEnergy_const_mul {N : ℕ} (c : ℂ) (a : Fin (N + 1) → ℂ)
    (s : Set Angle) (ω : LogMoments.SignVector N) :
    weightedRandomEnergy (fun k => c * a k) s ω = ‖c‖ ^ 2 * weightedRandomEnergy a s ω := by
  simp only [weightedRandomEnergy, weightedEnergy, weightedFourierSum_const_mul,
    norm_mul, mul_pow, integral_const_mul]

/-- Restoring an arbitrary amplitude bound gives the explicit factor `B²`
in the Hanson--Wright exponent. -/
theorem weightedRandomEnergy_lower_tail_of_norm_le {N : ℕ} (a : Fin (N + 1) → ℂ)
    {B : ℝ} (hB : 0 < B) (ha : ∀ k, ‖a k‖ ≤ B) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) (henergy : 0 < ∑ k, ‖a k‖ ^ 2) :
    (LogMoments.signMeasure N).real
      {ω | weightedRandomEnergy a s ω ≤ (∑ k, ‖a k‖ ^ 2) * angularMeasure.real s / 2} ≤
        2 * Real.exp (-((∑ k, ‖a k‖ ^ 2) * angularMeasure.real s) / (16384 * B ^ 2)) := by
  let b := fun k => a k / (B : ℂ)
  have hb : ∀ k, ‖b k‖ ≤ 1 := by
    intro k
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact (div_le_one₀ hB).mpr (ha k)
  have hnorm : ∑ k, ‖b k‖ ^ 2 = (∑ k, ‖a k‖ ^ 2) / B ^ 2 := by
    simp only [b, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB, div_pow]
    rw [Finset.sum_div]
  have hbpos : 0 < ∑ k, ‖b k‖ ^ 2 := by rw [hnorm]; positivity
  have hscale (ω : LogMoments.SignVector N) :
      weightedRandomEnergy a s ω = B ^ 2 * weightedRandomEnergy b s ω := by
    have heq : (fun k => (B : ℂ) * b k) = a := by
      ext k
      dsimp [b]
      field_simp [show (B : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hB.ne']
    simpa only [heq, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      weightedRandomEnergy_const_mul (B : ℂ) b s ω
  have htail := weightedRandomEnergy_lower_tail b hb s hs hbpos
  have hevent : {ω | weightedRandomEnergy a s ω ≤
      (∑ k, ‖a k‖ ^ 2) * angularMeasure.real s / 2} =
      {ω | weightedRandomEnergy b s ω ≤ (∑ k, ‖b k‖ ^ 2) * angularMeasure.real s / 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hscale, hnorm]
    have heq : (∑ k, ‖a k‖ ^ 2) / B ^ 2 * angularMeasure.real s / 2 =
        ((∑ k, ‖a k‖ ^ 2) * angularMeasure.real s / 2) / B ^ 2 := by ring
    rw [heq, le_div_iff₀ (sq_pos_of_pos hB), mul_comm (weightedRandomEnergy b s ω)]
  rw [hevent]
  convert htail using 1
  rw [hnorm]
  congr 2
  ring

end Erdos522.ArcEnergy

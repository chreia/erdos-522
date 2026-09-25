/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherCoordinates
import SLT.HansonWright
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Angular energy of finite Fourier sums

Integration over a measurable angular set produces a positive real Gram matrix.
Normalized Haar measure makes the full-circle Gram matrix the identity.
-/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal

namespace Erdos522
namespace ArcEnergy

abbrev Angle := AddCircle (1 : ℝ)

abbrev angularMeasure : Measure Angle := AddCircle.haarAddCircle

/-- A finite Fourier sum with real coefficients. -/
def fourierSum {N : ℕ} (x : Fin (N + 1) → ℝ) (θ : Angle) : ℂ :=
  ∑ k, x k • fourier (k : ℤ) θ

/-- Energy on an angular set, with normalized angular measure. -/
def energy {N : ℕ} (s : Set Angle) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∫ θ in s, ‖fourierSum x θ‖ ^ 2 ∂angularMeasure

/-- The real Gram matrix of Fourier monomials restricted to an angular set. -/
def gramMatrix (N : ℕ) (s : Set Angle) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => ∫ θ in s, inner ℝ (fourier (i : ℤ) θ) (fourier (j : ℤ) θ)
    ∂angularMeasure

lemma continuous_fourierSum {N : ℕ} (x : Fin (N + 1) → ℝ) :
    Continuous (fourierSum x) := by
  unfold fourierSum
  fun_prop

lemma integrable_norm_sq_fourierSum {N : ℕ} (x : Fin (N + 1) → ℝ) :
    Integrable (fun θ => ‖fourierSum x θ‖ ^ 2) angularMeasure :=
  ((continuous_fourierSum x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_fourier {N : ℕ} (i j : Fin (N + 1)) :
    Integrable (fun θ : Angle => inner ℝ (fourier (i : ℤ) θ) (fourier (j : ℤ) θ))
      angularMeasure :=
  ((fourier (i : ℤ)).continuous.inner (fourier (j : ℤ)).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma norm_sq_fourierSum {N : ℕ} (x : Fin (N + 1) → ℝ) (θ : Angle) :
    ‖fourierSum x θ‖ ^ 2 = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      inner ℝ (fourier (i : ℤ) θ) (fourier (j : ℤ) θ) * x i * x j := by
  rw [← real_inner_self_eq_norm_sq, fourierSum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The angular energy is exactly the quadratic form of its real Gram matrix. -/
theorem quadraticForm_gramMatrix {N : ℕ} (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    HansonWright.quadraticForm (gramMatrix N s) x = energy s x := by
  unfold HansonWright.quadraticForm gramMatrix energy
  simp_rw [norm_sq_fourierSum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_mul_const]
    · intro j _
      exact (((integrable_inner_fourier i j).restrict).mul_const _).mul_const _
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      (((integrable_inner_fourier i j).restrict).mul_const _).mul_const _)

lemma gramMatrix_symmetric (N : ℕ) (s : Set Angle) (i j : Fin (N + 1)) :
    gramMatrix N s i j = gramMatrix N s j i := by
  unfold gramMatrix
  congr 1
  ext θ
  exact real_inner_comm _ _

lemma gramMatrix_isHermitian (N : ℕ) (s : Set Angle) :
    (gramMatrix N s).IsHermitian := by
  ext i j
  simpa using gramMatrix_symmetric N s j i

lemma energy_nonneg {N : ℕ} (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    0 ≤ energy s x := integral_nonneg (fun _ => sq_nonneg _)

lemma gramMatrix_diagonal (N : ℕ) (s : Set Angle) (i : Fin (N + 1)) :
    gramMatrix N s i i = angularMeasure.real s := by
  simp [gramMatrix, fourier]

/-- The trace is the number of coefficients times the normalized angular length. -/
theorem trace_gramMatrix (N : ℕ) (s : Set Angle) :
    (gramMatrix N s).trace = (N + 1 : ℝ) * angularMeasure.real s := by
  simp [Matrix.trace, Matrix.diag, gramMatrix_diagonal]

/-- Parseval's identity in the normalization used for angular energy. -/
theorem energy_univ {N : ℕ} (x : Fin (N + 1) → ℝ) :
    energy Set.univ x = ∑ k, (x k) ^ 2 := by
  have heq : fourierSum x = LogMoments.fourierPolynomial
      (fun k => (x k : ℂ)) (fun _ => true) := by
    ext θ
    simp [fourierSum, LogMoments.fourierPolynomial_eq_sum, LogMoments.sign,
      Algebra.smul_def]
  simp only [energy, Measure.restrict_univ, heq,
    LogMoments.integral_norm_sq_fourierPolynomial, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Restricting the angular integral decreases the energy. -/
theorem energy_le_sum_sq {N : ℕ} (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    energy s x ≤ ∑ k, (x k) ^ 2 := by
  rw [← energy_univ x]
  unfold energy
  rw [Measure.restrict_univ]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (fun _ => sq_nonneg _)) (integrable_norm_sq_fourierSum x)

lemma dotProduct_gramMatrix {N : ℕ} (s : Set Angle) (x : Fin (N + 1) → ℝ) :
    star x ⬝ᵥ ((gramMatrix N s) *ᵥ x) = energy s x := by
  rw [← quadraticForm_gramMatrix]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, HansonWright.quadraticForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity of the angular Gram matrix. -/
theorem gramMatrix_posSemidef (N : ℕ) (s : Set Angle) :
    (gramMatrix N s).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gramMatrix_isHermitian N s)
  intro x
  rw [dotProduct_gramMatrix]
  exact energy_nonneg s x

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The normalized angular Gram matrix is a positive contraction. -/
theorem gramMatrix_le_one (N : ℕ) (s : Set Angle) :
    gramMatrix N s ≤ 1 := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (gramMatrix_isHermitian N s))
  intro x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_gramMatrix]
  have h := energy_le_sum_sq s x
  simpa [dotProduct, pow_two] using sub_nonneg.mpr h

/-- Squaring a positive contraction decreases it in the matrix order. -/
lemma gramMatrix_sq_le_self (N : ℕ) (s : Set Angle) :
    gramMatrix N s * gramMatrix N s ≤ gramMatrix N s := by
  have hc : Commute (gramMatrix N s) (1 - gramMatrix N s) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have h := hc.mul_nonneg (gramMatrix_posSemidef N s).nonneg
    (sub_nonneg.mpr (gramMatrix_le_one N s))
  simpa only [mul_sub, mul_one, sub_nonneg] using h

/-- The operator norm is the native Euclidean matrix norm. -/
theorem operatorNorm_gramMatrix_le_one (N : ℕ) (s : Set Angle) :
    HansonWright.operatorNorm (gramMatrix N s) ≤ 1 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (gramMatrix N s)
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (gramMatrix_isHermitian N s)
  change ‖T‖ ≤ 1
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  have heq : inner ℝ (T x) x = energy s (fun i => x i) := by
    rw [← quadraticForm_gramMatrix, HansonWright.quadraticForm_eq_inner_toEuclideanCLM]
  have hn : (∑ i, (x i) ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  have hnonneg := energy_nonneg s (fun i => x i)
  have hle := energy_le_sum_sq s (fun i => x i)
  rw [hn] at hle
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, heq,
    abs_of_nonneg (div_nonneg hnonneg (sq_nonneg _))]
  by_cases hx : x = 0
  · simp [hx]
  · exact (div_le_one₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr hle

/-- The squared Frobenius norm is bounded by the trace, uniformly in the angular set. -/
theorem frobeniusNormSq_gramMatrix_le_trace (N : ℕ) (s : Set Angle) :
    HansonWright.frobeniusNormSq (gramMatrix N s) ≤ (gramMatrix N s).trace := by
  have h := (Matrix.le_iff.mp (gramMatrix_sq_le_self N s)).trace_nonneg
  rw [Matrix.trace_sub] at h
  have heq : (gramMatrix N s * gramMatrix N s).trace =
      HansonWright.frobeniusNormSq (gramMatrix N s) := by
    calc
      _ = ((gramMatrix N s).conjTranspose * gramMatrix N s).trace := by
        rw [(gramMatrix_isHermitian N s).eq]
      _ = _ := HansonWright.matrix_trace_conjTranspose_mul_self_eq_frobeniusNormSq _
  rw [heq] at h
  linarith

lemma frobeniusNorm_gramMatrix_pos (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    0 < HansonWright.frobeniusNorm (gramMatrix N s) := by
  apply Real.sqrt_pos.mpr
  unfold HansonWright.frobeniusNormSq
  apply Finset.sum_pos'
  · intro i _
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · exact fun _ _ => sq_nonneg _
    · exact ⟨0, Finset.mem_univ _, by rw [gramMatrix_diagonal]; positivity⟩

lemma operatorNorm_gramMatrix_pos (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    0 < HansonWright.operatorNorm (gramMatrix N s) := by
  apply norm_pos_iff.mpr
  intro h
  have hz : gramMatrix N s = 0 := Matrix.toEuclideanCLM.injective (by simpa using h)
  have hdiag := congrArg (fun A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ => A 0 0) hz
  rw [gramMatrix_diagonal] at hdiag
  exact hs.ne' hdiag

private lemma hansonWright_constants :
    4 * Real.exp 1 ≤ (1024 : ℝ) ∧
      8 * Real.exp 1 ^ 3 ≤ (1024 : ℝ) ∧
      16 * Real.exp 1 ≤ (1024 : ℝ) ^ 2 ∧
      64 * Real.exp 1 ^ 2 ≤ (1024 : ℝ) := by
  have he0 := Real.exp_pos 1
  have he1 := Real.exp_one_lt_three
  have he2 : Real.exp 1 ^ 2 < (3 : ℝ) ^ 2 := pow_lt_pow_left₀ he1 he0.le (by decide)
  have he3 : Real.exp 1 ^ 3 < (3 : ℝ) ^ 3 := pow_lt_pow_left₀ he1 he0.le (by decide)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

/-- A unit-proxy Hanson--Wright bound for the real angular Gram matrix. -/
theorem centered_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    (s : Set Angle) (hs : 0 < angularMeasure.real s)
    (X : Fin (N + 1) → Ω → ℝ) (hind : ProbabilityTheory.iIndepFun X μ)
    (hsub : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) 1 μ) :
    μ.real {ω | (gramMatrix N s).trace / 2 ≤
      |HansonWright.centeredQuadraticForm μ (gramMatrix N s) X ω|} ≤
      2 * Real.exp (-(gramMatrix N s).trace / 16384) := by
  let T := (gramMatrix N s).trace
  have hT : 0 < T := by
    dsimp [T]
    rw [trace_gramMatrix]
    positivity
  have hF := frobeniusNorm_gramMatrix_pos N s hs
  have hO := operatorNorm_gramMatrix_pos N s hs
  have hFsq := frobeniusNormSq_gramMatrix_le_trace N s
  rw [← HansonWright.frobeniusNorm_sq] at hFsq
  have hO1 := operatorNorm_gramMatrix_le_one N s
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hansonWright_constants
  have h := HansonWright.hanson_wright_inequality (A := gramMatrix N s) (X := X)
    (K := 1) (C := 1024) (t := T / 2)
    (by norm_num) (by norm_num) hc1 hc2 hc3 hc4 hF hO hind
    (by
      have hproxy : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : ℝ≥0) = 1 := by ext; norm_num
      intro i
      rw [hproxy]
      exact hsub i) (by positivity)
  simp only [one_pow, one_mul] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hfirst : T / 4 ≤ (T / 2) ^ 2 / HansonWright.frobeniusNorm (gramMatrix N s) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hF)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hFsq hT.le]
  have hsecond : T / 4 ≤ T / 2 / HansonWright.operatorNorm (gramMatrix N s) := by
    apply (le_div_iff₀ hO).mpr
    nlinarith [mul_le_mul_of_nonneg_left hO1 hT.le]
  have hm : T / 4 ≤ min ((T / 2) ^ 2 /
      HansonWright.frobeniusNorm (gramMatrix N s) ^ 2)
      (T / 2 / HansonWright.operatorNorm (gramMatrix N s)) := le_min hfirst hsecond
  dsimp [T] at *
  linarith

/-- Arc energy for the finite product law of independent fair signs. -/
def randomEnergy (N : ℕ) (s : Set Angle) (ω : LogMoments.SignVector N) : ℝ :=
  energy s (fun i => LogMoments.realSign (ω i))

lemma randomEnergy_eq_quadraticForm (N : ℕ) (s : Set Angle)
    (ω : LogMoments.SignVector N) :
    randomEnergy N s ω = HansonWright.randomQuadraticForm (gramMatrix N s)
      (fun i ω => LogMoments.realSign (ω i)) ω :=
  (quadraticForm_gramMatrix s (fun i => LogMoments.realSign (ω i))).symm

/-- The mean of the random angular energy is the Gram trace. -/
theorem integral_randomEnergy (N : ℕ) (s : Set Angle) :
    (∫ ω, randomEnergy N s ω ∂LogMoments.signMeasure N) =
      (gramMatrix N s).trace := by
  simp_rw [randomEnergy_eq_quadraticForm, HansonWright.randomQuadraticForm,
    HansonWright.quadraticForm]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [mul_assoc, integral_const_mul, LogMoments.integral_mul_realSign_coordinates]
  simp

/-- Independent signs retain at least half the expected energy on an angular set
except with an exponentially small probability in its Gram trace. -/
theorem randomEnergy_lower_tail (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    (LogMoments.signMeasure N).real
      {ω | randomEnergy N s ω ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
        2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) := by
  rw [← trace_gramMatrix]
  have htail := centered_energy_tail s hs
    (fun i (ω : LogMoments.SignVector N) => LogMoments.realSign (ω i))
    (LogMoments.iIndepFun_realSign N) LogMoments.hasSubgaussianMGF_coordinate
  refine (measureReal_mono (fun ω hω => ?_)).trans htail
  change (gramMatrix N s).trace / 2 ≤
    |HansonWright.centeredQuadraticForm (LogMoments.signMeasure N)
      (gramMatrix N s) (fun i ω => LogMoments.realSign (ω i)) ω|
  simp only [HansonWright.centeredQuadraticForm, ← randomEnergy_eq_quadraticForm,
    integral_randomEnergy]
  have hneg := neg_le_abs (randomEnergy N s ω - (gramMatrix N s).trace)
  change randomEnergy N s ω ≤ (gramMatrix N s).trace / 2 at hω
  linarith

/-- The angular arc of half-width `h` radians about `θ`. -/
def arc (θ : Angle) (h : ℝ) : Set Angle :=
  Metric.closedBall θ (h / (2 * Real.pi))

lemma measurableSet_arc (θ : Angle) (h : ℝ) : MeasurableSet (arc θ h) :=
  measurableSet_closedBall

/-- Normalized angular measure converts radians to turns. -/
theorem angularMeasure_arc (θ : Angle) {h : ℝ} (hh : 0 ≤ h) (hπ : h ≤ Real.pi) :
    angularMeasure.real (arc θ h) = h / Real.pi := by
  have hv : angularMeasure = (volume : Measure Angle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  rw [Measure.real, hv, arc, AddCircle.volume_closedBall]
  have hdiv : 2 * (h / (2 * Real.pi)) = h / Real.pi := by ring
  rw [hdiv, min_eq_right ((div_le_one₀ Real.pi_pos).mpr hπ),
    ENNReal.toReal_ofReal (div_nonneg hh Real.pi_pos.le)]

/-- The logarithmic arc scale sufficient for the explicit sign-energy estimate. -/
def arcScale : ℝ := 262144 * Real.pi

/-- At the logarithmic arc scale the lower-tail probability is at most `2/N^16`. -/
theorem randomEnergy_arc_lower_tail (N : ℕ) (hN : 2 ≤ N) (θ : Angle)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (LogMoments.signMeasure N).real
      {ω | randomEnergy N (arc θ (arcScale * Real.log N / N)) ω ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      2 / (N : ℝ) ^ 16 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hlog := Real.log_pos hN1
  have hscale : 0 < arcScale := by unfold arcScale; positivity
  have hwidth : 0 < arcScale * Real.log N / N := by positivity
  have hmass := angularMeasure_arc θ hwidth.le hh
  have hmpos : 0 < angularMeasure.real (arc θ (arcScale * Real.log N / N)) := by
    rw [hmass]
    positivity
  have htail := randomEnergy_lower_tail N (arc θ (arcScale * Real.log N / N)) hmpos
  rw [hmass] at htail
  refine htail.trans ?_
  have htrace : (262144 : ℝ) * Real.log N ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) := by
    unfold arcScale
    field_simp
    nlinarith [Real.pi_pos]
  calc
    2 * Real.exp (-((N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi)) / 16384)
        ≤ 2 * Real.exp (-(16 * Real.log N)) := by
          gcongr
          linarith
    _ = 2 / (N : ℝ) ^ 16 := by
      rw [Real.exp_neg, show (16 : ℝ) = (16 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hN0, div_eq_mul_inv]

/-- A finite family costs exactly its cardinality in the energy union bound. -/
theorem simultaneous_arc_energy_tail (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (LogMoments.signMeasure N).real
      {ω | ∃ i, randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      (Fintype.card ι : ℝ) * (2 / (N : ℝ) ^ 16) := by
  rw [show {ω : LogMoments.SignVector N | ∃ i,
      randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} =
    ⋃ i, {ω | randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} by ext ω; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => randomEnergy_arc_lower_tail N hN (θ i) hh)

/-- Energy above a constant level forces a point above that level on the same set. -/
theorem exists_large_value_of_energy_gt {N : ℕ} (s : Set Angle) (hs : MeasurableSet s)
    (x : Fin (N + 1) → ℝ) (b : ℝ)
    (henergy : angularMeasure.real s * b < energy s x) :
    ∃ θ ∈ s, b < ‖fourierSum x θ‖ ^ 2 := by
  by_contra h
  push Not at h
  have hi := setIntegral_mono_on (integrable_norm_sq_fourierSum x).integrableOn
    (integrableOn_const (by finiteness)) hs h
  rw [setIntegral_const, smul_eq_mul] at hi
  exact (not_le.mpr henergy) hi

lemma arc_family_failure_budget {N J : ℕ} (hN : 2 ≤ N) (hJ : J ≤ 8 * N) :
    (J : ℝ) * (2 / (N : ℝ) ^ 16) ≤ 1 / (N : ℝ) ^ 3 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hJr : (J : ℝ) ≤ 8 * N := by exact_mod_cast hJ
  have hpow : (16 : ℝ) ≤ (N : ℝ) ^ 12 := by
    calc
      (16 : ℝ) ≤ 2 ^ 12 := by norm_num
      _ ≤ (N : ℝ) ^ 12 := by gcongr
  calc
    (J : ℝ) * (2 / (N : ℝ) ^ 16) ≤ (8 * N) * (2 / (N : ℝ) ^ 16) := by gcongr
    _ = (16 / (N : ℝ) ^ 12) * (1 / (N : ℝ) ^ 3) := by field_simp; ring
    _ ≤ 1 * (1 / (N : ℝ) ^ 3) := by
      gcongr
      exact (div_le_one₀ (pow_pos hN0 _)).mpr hpow
    _ = 1 / (N : ℝ) ^ 3 := one_mul _

/-- The angular family used for local root counts has total failure at most `N⁻³`. -/
theorem simultaneous_arc_energy_tail_le (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (LogMoments.signMeasure N).real
      {ω | ∃ i, randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      1 / (N : ℝ) ^ 3 :=
  (simultaneous_arc_energy_tail N hN θ hh).trans (arc_family_failure_budget hN hcard)

/-- A finite angular family simultaneously supplies large polynomial values,
with failure at most `N⁻³`. -/
theorem simultaneous_large_values (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (LogMoments.signMeasure N).real
      {ω | ∃ i, ∀ t ∈ arc (θ i) (arcScale * Real.log N / N),
        ‖fourierSum (fun k => LogMoments.realSign (ω k)) t‖ ^ 2 ≤ (N + 1 : ℝ) / 2} ≤
      1 / (N : ℝ) ^ 3 := by
  refine (measureReal_mono (fun ω hω => ?_)).trans
    (simultaneous_arc_energy_tail_le N hN θ hcard hh)
  obtain ⟨i, hi⟩ := hω
  refine ⟨i, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hN)
  have hwidth : 0 ≤ arcScale * Real.log N / N := by
    unfold arcScale
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hN1)) hN0.le
  have hm := angularMeasure_arc (θ i) hwidth hh
  have hint := setIntegral_mono_on
    (integrable_norm_sq_fourierSum (fun k => LogMoments.realSign (ω k))).integrableOn
    (integrableOn_const (by finiteness)) (measurableSet_arc _ _) hi
  rw [setIntegral_const, smul_eq_mul, hm] at hint
  change energy _ _ ≤ _
  unfold energy
  convert hint using 1
  ring

end ArcEnergy
end Erdos522

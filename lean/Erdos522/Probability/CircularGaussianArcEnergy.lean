/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.AngularGramMatrix
import Erdos522.Probability.CircularGaussianRepresentation
import Erdos522.Probability.GaussianArcEnergy
import Erdos522.Probability.SymmetricArcEnergy

/-!
# Angular energy for circular Gaussian polynomials

The real and imaginary coefficient coordinates form one real quadratic form.
Parseval makes its angular Gram matrix a positive contraction, and its trace
is exactly the expected complex angular energy.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Erdos522

/-- A single real Gaussian array assembled into circular complex coefficients. -/
def circularGaussianRealification (n : ℕ) : (Fin (n + n) → ℝ) ≃ᵐ (Fin n → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) finSumFinEquiv.symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).trans
      (circularGaussianCoefficientVectorEquiv n))

@[simp]
theorem circularGaussianRealification_apply (n : ℕ) (g : Fin (n + n) → ℝ) (k : Fin n) :
    circularGaussianRealification n g k =
      ((g (Fin.castAdd n k) : ℂ) + (g (Fin.natAdd n k) : ℂ) * Complex.I) /
        (Real.sqrt 2 : ℂ) := by
  simp [circularGaussianRealification, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft]

theorem measurePreserving_circularGaussianRealification (n : ℕ) :
    MeasurePreserving (circularGaussianRealification n) (gaussianCoefficientMeasure (n + n))
      (Measure.pi (fun _ : Fin n => circularComplexGaussian)) := by
  exact (measurePreserving_circularGaussianCoefficientVectors n).comp
    ((measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)).comp
      (measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)
        finSumFinEquiv.symm))

namespace CircularGaussianArcEnergy
open ArcEnergy

lemma integrable_norm_sq_complexFourierSum {N : ℕ} (a : Fin (N + 1) → ℂ) :
    Integrable (fun θ => ‖complexFourierSum a θ‖ ^ 2) angularMeasure := by
  have hc : Continuous (fun θ : Angle => ‖complexFourierSum a θ‖ ^ 2) := by
    unfold complexFourierSum
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The real coordinate directions of complex Fourier monomials. -/
def coordinateBasis (N : ℕ) : Fin ((N + 1) + (N + 1)) → Angle → ℂ :=
  Fin.addCases (fun k θ => fourier (k : ℤ) θ / (Real.sqrt 2 : ℂ))
    (fun k θ => Complex.I * fourier (k : ℤ) θ / (Real.sqrt 2 : ℂ))

lemma continuous_coordinateBasis (N : ℕ) (k : Fin ((N + 1) + (N + 1))) :
    Continuous (coordinateBasis N k) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [coordinateBasis, Fin.addCases_left, Fin.addCases_right] <;> fun_prop

theorem coordinate_sum_eq (N : ℕ) (g : Fin ((N + 1) + (N + 1)) → ℝ) (θ : Angle) :
    AngularGram.finiteSum (coordinateBasis N) g θ =
      complexFourierSum (circularGaussianRealification (N + 1) g) θ := by
  rw [AngularGram.finiteSum, Fin.sum_univ_add]
  simp only [coordinateBasis,
    Fin.addCases_left, Fin.addCases_right, Complex.real_smul,
    complexFourierSum, circularGaussianRealification_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma norm_sq_circularGaussianRealification (n : ℕ) (g : Fin (n + n) → ℝ) (k : Fin n) :
    ‖circularGaussianRealification n g k‖ ^ 2 =
      (g (Fin.castAdd n k) ^ 2 + g (Fin.natAdd n k) ^ 2) / 2 := by
  rw [circularGaussianRealification_apply, norm_div, div_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- The two real coordinate families have exact full-circle frame bound `1/2`. -/
theorem coordinate_energy_univ (N : ℕ) (g : Fin ((N + 1) + (N + 1)) → ℝ) :
    AngularGram.energy (coordinateBasis N) Set.univ g = (∑ k, g k ^ 2) / 2 := by
  have he (θ : Angle) : complexFourierSum (circularGaussianRealification (N + 1) g) θ =
      LogMoments.fourierPolynomial (circularGaussianRealification (N + 1) g)
        (fun _ => true) θ := by
    simp [complexFourierSum, LogMoments.fourierPolynomial_eq_sum, LogMoments.sign]
  simp only [AngularGram.energy, coordinate_sum_eq, Measure.restrict_univ, he,
    LogMoments.integral_norm_sq_fourierPolynomial, norm_sq_circularGaussianRealification]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  exact (Fin.sum_univ_add (fun k => g k ^ 2)).symm

lemma coordinate_frame_bound (N : ℕ) (g : Fin ((N + 1) + (N + 1)) → ℝ) :
    AngularGram.energy (coordinateBasis N) Set.univ g ≤ ∑ k, g k ^ 2 := by
  rw [coordinate_energy_univ]
  have h : 0 ≤ ∑ k, g k ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- Every real coordinate direction has squared modulus `1/2`. -/
lemma norm_sq_coordinateBasis (N : ℕ) (k : Fin ((N + 1) + (N + 1))) (θ : Angle) :
    ‖coordinateBasis N k θ‖ ^ 2 = 1 / 2 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [coordinateBasis, Fin.addCases_left, Fin.addCases_right] <;>
    simp [fourier_apply,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem trace_coordinateGram (N : ℕ) (s : Set Angle) :
    (AngularGram.gramMatrix (coordinateBasis N) s).trace =
      (N + 1 : ℝ) * angularMeasure.real s := by
  simp only [AngularGram.trace_gramMatrix, norm_sq_coordinateBasis, integral_const,
    smul_eq_mul, measureReal_restrict_apply_univ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The expected coordinate energy equals the angular Gram trace. -/
theorem integral_coordinate_energy (N : ℕ) (s : Set Angle) :
    (∫ g, AngularGram.energy (coordinateBasis N) s g
      ∂gaussianCoefficientMeasure ((N + 1) + (N + 1))) =
      (AngularGram.gramMatrix (coordinateBasis N) s).trace := by
  have hL (i : Fin ((N + 1) + (N + 1))) :
      MemLp (fun g : Fin ((N + 1) + (N + 1)) → ℝ => g i) 2
        (gaussianCoefficientMeasure ((N + 1) + (N + 1))) :=
    (hasSubgaussianMGF_gaussian_coordinate _ i).memLp 2
  have hi (i j : Fin ((N + 1) + (N + 1))) : Integrable
      (fun g : Fin ((N + 1) + (N + 1)) → ℝ =>
        AngularGram.gramMatrix (coordinateBasis N) s i j * (g i * g j))
      (gaussianCoefficientMeasure ((N + 1) + (N + 1))) :=
    ((hL i).integrable_mul (hL j)).const_mul _
  simp only [← AngularGram.quadraticForm_gramMatrix _ (continuous_coordinateBasis N),
    HansonWright.quadraticForm]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum _ (fun j _ => by simpa only [mul_assoc] using hi i j))]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => by simpa only [mul_assoc] using hi i j)]
  simp_rw [mul_assoc, integral_const_mul, integral_mul_gaussian_coordinates]
  simp

/-- Independent real coordinates retain half their expected complex arc energy. -/
theorem coordinate_energy_lower_tail (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    (gaussianCoefficientMeasure ((N + 1) + (N + 1))).real
      {g | AngularGram.energy (coordinateBasis N) s g ≤
        (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
      2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) := by
  rw [← trace_coordinateGram]
  have ht : 0 < (AngularGram.gramMatrix (coordinateBasis N) s).trace := by
    rw [trace_coordinateGram]
    positivity
  have htail := AngularGram.centered_energy_tail (coordinateBasis N)
    (continuous_coordinateBasis N) (coordinate_frame_bound N) s ht
    (fun i (g : Fin ((N + 1) + (N + 1)) → ℝ) => g i)
    (iIndepFun_gaussian_coordinates _) (hasSubgaussianMGF_gaussian_coordinate _)
  refine (measureReal_mono (fun g hg => ?_)).trans htail
  change _ ≤ |HansonWright.centeredQuadraticForm _ _ _ g|
  have he (g : Fin ((N + 1) + (N + 1)) → ℝ) :
      HansonWright.randomQuadraticForm (AngularGram.gramMatrix (coordinateBasis N) s)
        (fun i g => g i) g = AngularGram.energy (coordinateBasis N) s g :=
    AngularGram.quadraticForm_gramMatrix _ (continuous_coordinateBasis N) s g
  simp only [HansonWright.centeredQuadraticForm, he, integral_coordinate_energy]
  have hneg := neg_le_abs (AngularGram.energy (coordinateBasis N) s g -
    (AngularGram.gramMatrix (coordinateBasis N) s).trace)
  change AngularGram.energy (coordinateBasis N) s g ≤
    (AngularGram.gramMatrix (coordinateBasis N) s).trace / 2 at hg
  linarith

/-- The actual circular Gaussian product law satisfies the half-energy lower tail. -/
theorem complexEnergy_lower_tail (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {a | complexEnergy a s ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
      2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) := by
  rw [← (measurePreserving_circularGaussianRealification (N + 1)).map_eq,
    measureReal_def, (circularGaussianRealification (N + 1)).map_apply]
  have he : circularGaussianRealification (N + 1) ⁻¹'
      {a | complexEnergy a s ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} =
      {g | AngularGram.energy (coordinateBasis N) s g ≤
        (N + 1 : ℝ) * angularMeasure.real s / 2} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, AngularGram.energy, coordinate_sum_eq,
      complexEnergy]
  rw [he]
  exact coordinate_energy_lower_tail N s hs

/-- At the logarithmic arc scale the lower-tail probability is at most `2/N^16`. -/
theorem complexEnergy_arc_lower_tail (N : ℕ) (hN : 2 ≤ N) (θ : Angle)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {ω | complexEnergy ω (arc θ (arcScale * Real.log N / N)) ≤
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
  have htail := complexEnergy_lower_tail N (arc θ (arcScale * Real.log N / N)) hmpos
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
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {ω | ∃ i, complexEnergy ω (arc (θ i) (arcScale * Real.log N / N)) ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      (Fintype.card ι : ℝ) * (2 / (N : ℝ) ^ 16) := by
  rw [show {ω : Fin (N + 1) → ℂ | ∃ i,
      complexEnergy ω (arc (θ i) (arcScale * Real.log N / N)) ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} =
    ⋃ i, {ω | complexEnergy ω (arc (θ i) (arcScale * Real.log N / N)) ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} by ext ω; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => complexEnergy_arc_lower_tail N hN (θ i) hh)


/-- The angular family used for local root counts has total failure at most `N⁻³`. -/
theorem simultaneous_arc_energy_tail_le (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {ω | ∃ i, complexEnergy ω (arc (θ i) (arcScale * Real.log N / N)) ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      1 / (N : ℝ) ^ 3 :=
  (simultaneous_arc_energy_tail N hN θ hh).trans (arc_family_failure_budget hN hcard)

/-- A finite angular family simultaneously supplies large polynomial values,
with failure at most `N⁻³`. -/
theorem simultaneous_large_values (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (Measure.pi (fun _ : Fin (N + 1) => circularComplexGaussian)).real
      {ω | ∃ i, ∀ t ∈ arc (θ i) (arcScale * Real.log N / N),
        ‖complexFourierSum ω t‖ ^ 2 ≤ (N + 1 : ℝ) / 2} ≤
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
    (integrable_norm_sq_complexFourierSum ω).integrableOn
    (integrableOn_const (by finiteness)) (measurableSet_arc _ _) hi
  rw [setIntegral_const, smul_eq_mul, hm] at hint
  change complexEnergy _ _ ≤ _
  unfold complexEnergy
  convert hint using 1
  ring

end CircularGaussianArcEnergy
end Erdos522

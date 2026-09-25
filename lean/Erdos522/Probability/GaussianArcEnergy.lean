/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianTails
import Erdos522.Probability.ArcEnergy

/-!
# Arc energy for real Gaussian polynomials

Independent standard Gaussian coordinates have unit sub-Gaussian proxy and
identity second moments. The angular Gram form therefore satisfies the same
explicit Hanson–Wright lower-tail estimate as a normalized bounded model.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace Erdos522

/-- The coordinate projections under the Gaussian coefficient product law are independent. -/
theorem iIndepFun_gaussian_coordinates (n : ℕ) :
    iIndepFun (fun k (g : Fin n → ℝ) => g k) (gaussianCoefficientMeasure n) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Each standard Gaussian coordinate has unit sub-Gaussian proxy. -/
theorem hasSubgaussianMGF_gaussian_coordinate (n : ℕ) (k : Fin n) :
    HasSubgaussianMGF (fun g : Fin n → ℝ => g k) 1 (gaussianCoefficientMeasure n) := by
  apply (HasSubgaussianMGF.id_map_iff (measurable_pi_apply k).aemeasurable).mp
  rw [gaussianCoefficientMeasure, (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) k).map_eq]
  exact HansonWright.hasSubgaussianMGF_id_gaussianReal_zero_one

/-- A standard Gaussian coordinate has mean zero. -/
theorem integral_gaussian_coordinate (n : ℕ) (k : Fin n) :
    (∫ g, g k ∂gaussianCoefficientMeasure n) = 0 := by
  have h := integral_map (μ := gaussianCoefficientMeasure n) (f := fun x : ℝ => x)
    (measurable_pi_apply k).aemeasurable (by fun_prop)
  rw [gaussianCoefficientMeasure,
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) k).map_eq,
    integral_id_gaussianReal] at h
  exact h.symm

/-- Gaussian coordinates have identity second-moment matrix. -/
theorem integral_mul_gaussian_coordinates (n : ℕ) (i j : Fin n) :
    (∫ g, g i * g j ∂gaussianCoefficientMeasure n) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [realGaussianSum, pow_two] using
      integral_sq_realGaussianSum (fun k : Fin n => if k = i then 1 else 0)
  · rw [ite_eq_right hij, (iIndepFun_gaussian_coordinates n).indepFun hij |>.integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,
      integral_gaussian_coordinate, integral_gaussian_coordinate, mul_zero]

namespace GaussianArcEnergy
open ArcEnergy

/-- The angular energy of the actual Gaussian coefficient vector. -/
def randomEnergy (N : ℕ) (s : Set Angle) (g : Fin (N + 1) → ℝ) : ℝ := energy s g

/-- The expected Gaussian arc energy is its deterministic Gram trace. -/
theorem integral_randomEnergy (N : ℕ) (s : Set Angle) :
    (∫ g, randomEnergy N s g ∂gaussianCoefficientMeasure (N + 1)) = (gramMatrix N s).trace := by
  have hL (i : Fin (N + 1)) : MemLp (fun g : Fin (N + 1) → ℝ => g i) 2
      (gaussianCoefficientMeasure (N + 1)) := by
    simpa using (hasSubgaussianMGF_gaussian_coordinate (N + 1) i).memLp 2
  have hi (i j : Fin (N + 1)) : Integrable (fun g : Fin (N + 1) → ℝ =>
      (gramMatrix N s) i j * (g i * g j)) (gaussianCoefficientMeasure (N + 1)) :=
    ((hL i).integrable_mul (hL j)).const_mul _
  simp only [randomEnergy, ← quadraticForm_gramMatrix, HansonWright.quadraticForm]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum _ (fun j _ => by simpa only [mul_assoc] using hi i j))]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => by simpa only [mul_assoc] using hi i j)]
  simp_rw [mul_assoc, integral_const_mul, integral_mul_gaussian_coordinates]
  simp

/-- Gaussian angular energy is at least half its mean apart from an explicit exponential tail. -/
theorem randomEnergy_lower_tail (N : ℕ) (s : Set Angle)
    (hs : 0 < angularMeasure.real s) :
    (gaussianCoefficientMeasure (N + 1)).real
      {g | randomEnergy N s g ≤ (N + 1 : ℝ) * angularMeasure.real s / 2} ≤
        2 * Real.exp (-((N + 1 : ℝ) * angularMeasure.real s) / 16384) := by
  rw [← trace_gramMatrix]
  have htail := centered_energy_tail s hs (fun i (g : Fin (N + 1) → ℝ) => g i)
    (iIndepFun_gaussian_coordinates _) (hasSubgaussianMGF_gaussian_coordinate _)
  refine (measureReal_mono (fun g hg => ?_)).trans htail
  change (gramMatrix N s).trace / 2 ≤
    |HansonWright.centeredQuadraticForm (gaussianCoefficientMeasure (N + 1))
      (gramMatrix N s) (fun i g => g i) g|
  have he (g : Fin (N + 1) → ℝ) :
      HansonWright.randomQuadraticForm (gramMatrix N s) (fun i g => g i) g = randomEnergy N s g :=
    quadraticForm_gramMatrix s g
  simp only [HansonWright.centeredQuadraticForm, he, integral_randomEnergy]
  have hneg := neg_le_abs (randomEnergy N s g - (gramMatrix N s).trace)
  change randomEnergy N s g ≤ (gramMatrix N s).trace / 2 at hg
  linarith

/-- At the logarithmic arc scale the lower-tail probability is at most `2/N^16`. -/
theorem randomEnergy_arc_lower_tail (N : ℕ) (hN : 2 ≤ N) (θ : Angle)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (gaussianCoefficientMeasure (N + 1)).real
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
    (gaussianCoefficientMeasure (N + 1)).real
      {ω | ∃ i, randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      (Fintype.card ι : ℝ) * (2 / (N : ℝ) ^ 16) := by
  rw [show {ω : Fin (N + 1) → ℝ | ∃ i,
      randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} =
    ⋃ i, {ω | randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
      (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} by ext ω; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => randomEnergy_arc_lower_tail N hN (θ i) hh)


/-- The angular family used for local root counts has total failure at most `N⁻³`. -/
theorem simultaneous_arc_energy_tail_le (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (gaussianCoefficientMeasure (N + 1)).real
      {ω | ∃ i, randomEnergy N (arc (θ i) (arcScale * Real.log N / N)) ω ≤
        (N + 1 : ℝ) * (arcScale * Real.log N / N / Real.pi) / 2} ≤
      1 / (N : ℝ) ^ 3 :=
  (simultaneous_arc_energy_tail N hN θ hh).trans (arc_family_failure_budget hN hcard)

/-- A finite angular family simultaneously supplies large polynomial values,
with failure at most `N⁻³`. -/
theorem simultaneous_large_values (N : ℕ) (hN : 2 ≤ N)
    {ι : Type*} [Fintype ι] (θ : ι → Angle) (hcard : Fintype.card ι ≤ 8 * N)
    (hh : arcScale * Real.log N / N ≤ Real.pi) :
    (gaussianCoefficientMeasure (N + 1)).real
      {ω | ∃ i, ∀ t ∈ arc (θ i) (arcScale * Real.log N / N),
        ‖fourierSum ω t‖ ^ 2 ≤ (N + 1 : ℝ) / 2} ≤
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
    (integrable_norm_sq_fourierSum ω).integrableOn
    (integrableOn_const (by finiteness)) (measurableSet_arc _ _) hi
  rw [setIntegral_const, smul_eq_mul, hm] at hint
  change energy _ _ ≤ _
  unfold energy
  convert hint using 1
  ring

end GaussianArcEnergy
end Erdos522

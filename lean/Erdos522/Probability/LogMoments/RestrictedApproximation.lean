/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.PartitionFourierApproximation
import Erdos522.Probability.LogMoments.DistinctSpectrum

/-!
# Restricted energy and local exponential approximation

A measurable set of positive measure determines a shift scale uniformly over
normalized coefficient vectors. Each vector then has a distinct approximate
spectrum. On any fixed uniform partition at a larger scale, the local
exponential approximants have a common error whose squared mean is bounded
by the Fourier energy on the original set.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- The explicit squared-error constant for approximation of order `n`. -/
def restrictedApproximationConstant (n : ℕ) (δ : ℝ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * n) * (8 * ((n : ℝ) + 1) / δ) *
    (1 / spectralEnergyCutoff n + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n))

theorem restrictedApproximationConstant_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < restrictedApproximationConstant n δ := by
  have := spectralEnergyCutoff_pos n
  unfold restrictedApproximationConstant
  positivity

/-- A distinct weighted spectrum gives local approximants with an explicit
restricted-energy majorant at its prescribed scale. -/
theorem exists_fourier_approximation_of_distinct_spectrum {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (E : Set (SignVector N × AddCircle (1 : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) (Λ : Multiset ℝ) (hΛ : Λ.Nodup) (hcard : Λ.card ≤ n)
    (henergy : (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
      2 * (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E *
        (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)) *
        (1 / spectralEnergyCutoff n + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n))) :
    ∃ (m : ℕ) (ξ : Fin m → ℝ), m ≤ n ∧ Function.Injective ξ ∧
      ∀ (q : ℕ), 0 < q → ∀ M : ℝ, 1 ≤ M → 1 / (q : ℝ) = M * τ →
        ∃ Φ : SignVector N × ℝ → ℝ,
          (∀ z, 0 ≤ Φ z) ∧ MemLp Φ 2 (realFourierMeasure N) ∧
          (∫ z, Φ z ^ 2 ∂realFourierMeasure N) ≤
            restrictedApproximationConstant n ((fourierMeasure N).real E) *
              (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∧
          ∀ i : Fin q, ∃ P : SignVector N → ℝ → ℂ,
            (∀ ω, P ω ∈ exponentialSpan (Set.range ξ)) ∧
            ∀ ω x, x ∈ unitIntervalCell i →
              ‖realFourier a (ω, x) - P ω x‖ ≤ M ^ n * Φ (ω, x) := by
  classical
  let m := Λ.toList.length
  let ξ : Fin m → ℝ := Λ.toList.get
  have hm : m ≤ n := by simpa only [m, Multiset.length_toList] using hcard
  have hξ : Function.Injective ξ := by
    apply List.Nodup.injective_get
    apply Multiset.coe_nodup.mp
    simpa only [Multiset.coe_toList] using hΛ
  have hΛeq : (List.ofFn ξ : Multiset ℝ) = Λ := by
    simp only [ξ, List.ofFn_get, Multiset.coe_toList]
  refine ⟨m, ξ, hm, hξ, fun q hq M hM hscale => ?_⟩
  refine ⟨fourierApproximationError a τ ξ q,
    fourierApproximationError_nonneg a hτ.le ξ q,
    memLp_fourierApproximationError a τ ξ hq, ?_, ?_⟩
  · have hbound := integral_fourierApproximationError_sq_le a hτ ξ hq
    rw [hΛeq] at hbound
    have hW : 0 ≤ ∑ k, ‖a k‖ ^ 2 * spectralWeight τ Λ k.val ^ 2 :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hfactor : ((m : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * m) ≤
        ((n : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * n) := by
      gcongr
      linarith [Real.pi_gt_three]
    calc
      _ ≤ (((m : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * m)) *
          ∑ k, ‖a k‖ ^ 2 * spectralWeight τ Λ k.val ^ 2 := by
            simpa only [mul_assoc] using hbound
      _ ≤ (((n : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * n)) *
          ∑ k, ‖a k‖ ^ 2 * spectralWeight τ Λ k.val ^ 2 :=
            mul_le_mul_of_nonneg_right hfactor hW
      _ ≤ (((n : ℝ) + 1) ^ 2 * (6 * Real.pi) ^ (2 * n)) *
          (2 * (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E *
            (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N)) *
            (1 / spectralEnergyCutoff n +
              1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n))) :=
            mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by unfold restrictedApproximationConstant; ring
  · intro i
    obtain ⟨P, hP, herror⟩ := exists_partition_fourier_approximation a hτ hM ξ hξ
      hq hscale i
    refine ⟨P, hP, fun ω x hx => (herror ω x hx).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hm)
      (fourierApproximationError_nonneg a hτ.le ξ q (ω, x))


/-- Restricted Fourier energy controls local exponential approximation, with
a shift scale independent of the normalized coefficients. -/
theorem exists_restricted_fourier_approximation {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (p : ℕ) (hp : 1 ≤ p) :
    let n := shiftOrder ((fourierMeasure N).real E) p
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ a : Fin (N + 1) → ℂ, (∑ k, ‖a k‖ ^ 2 = 1) →
      ∃ (m : ℕ) (ξ : Fin m → ℝ), m ≤ n ∧ Function.Injective ξ ∧
        ∀ (q : ℕ), 0 < q → ∀ M : ℝ, 1 ≤ M → 1 / (q : ℝ) = M * τ →
          ∃ Φ : SignVector N × ℝ → ℝ,
            (∀ z, 0 ≤ Φ z) ∧ MemLp Φ 2 (realFourierMeasure N) ∧
            (∫ z, Φ z ^ 2 ∂realFourierMeasure N) ≤
              restrictedApproximationConstant n ((fourierMeasure N).real E) *
                (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) ∧
            ∀ i : Fin q, ∃ P : SignVector N → ℝ → ℂ,
              (∀ ω, P ω ∈ exponentialSpan (Set.range ξ)) ∧
              ∀ ω x, x ∈ unitIntervalCell i →
                ‖realFourier a (ω, x) - P ω x‖ ≤ M ^ n * Φ (ω, x) := by
  classical
  dsimp only
  let n := shiftOrder ((fourierMeasure N).real E) p
  obtain ⟨τ₀, hτ₀, hsmall⟩ := exists_quantitative_small_shifts E hE hpos p hp
  let τ := min τ₀ 1
  have hτ : 0 < τ := lt_min hτ₀ (by norm_num)
  refine ⟨τ, hτ, min_le_right _ _, fun a ha => ?_⟩
  have hB : 0 < (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E) *
      (∫ z in E, ‖randomFourier a z‖ ^ 2 ∂fourierMeasure N) :=
    mul_pos (div_pos (by positivity) hpos) (restricted_fourier_energy_pos a ha E hpos)
  obtain ⟨Λ, hΛ, hcard, henergy⟩ := exists_distinct_weighted_spectrum_of_shift_relations a
    hτ hB (fun t => hsmall t.val t.property.1 (t.property.2.trans_le (min_le_left _ _)) a)
  exact exists_fourier_approximation_of_distinct_spectrum a E hτ Λ hΛ hcard henergy

end Erdos522.LogMoments

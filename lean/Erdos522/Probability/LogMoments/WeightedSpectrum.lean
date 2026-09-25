/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpectralConcentration
import Erdos522.Probability.LogMoments.ShiftPolynomials
import Erdos522.Analysis.SpectralRootPhases
import Erdos522.Probability.LogMoments.SpectralWeights

/-!
# Weighted approximate spectra of finite Fourier sums

A short-shift relation supplies a polynomial whose root phases describe the
approximate spectrum. Reciprocal-progression separation gives a lower bound
for the multiplier on the intervals carrying most of the coefficient energy.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace Erdos522.LogMoments

/-- At one shift time a normalized relation controls the product of clipped
distances to at most `n` frequencies throughout the short interval union. -/
theorem exists_weighted_shift_relation {N n : ℕ}
    (a : Fin (N + 1) → ℂ) (T : Finset ℝ) (hcard : T.card ≤ n)
    {τ B : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ t : Set.Ioo (0 : ℝ) τ, ∃ c : Fin (n + 1) → ℂ,
      (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • (t.val : AddCircle (1 : ℝ))) q)‖ ^ 2
          ∂fourierMeasure N) ≤ B) :
    let δ : ℝ := 1 / (8 * ((n : ℝ) + 1) ^ 2)
    ∃ (t : ℝ) (c : Fin (n + 1) → ℂ) (Λ : Multiset ℝ),
      t ∈ Set.Ioo (τ / 2) τ ∧ Λ.card ≤ n ∧
      (∑ k, ‖a k‖ ^ 2 * ‖shiftMultiplier c (t : AddCircle (1 : ℝ)) k.val‖ ^ 2) ≤ B ∧
      ∀ x ∈ finiteIntervalUnion T (δ / τ),
        δ ^ n * (Λ.map fun ξ => min 1 (τ * |x - ξ|)).prod ≤
          ‖(Polynomial.ofFn (n + 1) c).eval (angularCharacter (t * x))‖ := by
  classical
  dsimp only
  let δ : ℝ := 1 / (8 * ((n : ℝ) + 1) ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one₀ (by positivity)).mpr
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  have hr : 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) = δ / τ := by
    dsimp [δ]
    rw [div_div]
  obtain ⟨t, ht, hsep⟩ := exists_time_separating_short_spectral_intervals T n hcard τ hτ
  rw [hr] at hsep
  obtain ⟨c, hc, henergy⟩ := hsmall ⟨t, (lt_trans (half_pos hτ) ht.1), ht.2⟩
  obtain ⟨z₀, hz₀, hlarge⟩ := exists_unitCircle_polynomial_norm_ge_one c hc
  obtain ⟨ξ, hξ⟩ := exists_root_phases_on_intervals (Polynomial.ofFn (n + 1) c) T
    hτ ht.1.le hδ.le hδ1 hsep hz₀ hlarge
  let P := Polynomial.ofFn (n + 1) c
  have hdegree : P.natDegree ≤ n := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) c)
  refine ⟨t, c, P.roots.map ξ, ht, ?_, ?_, ?_⟩
  · simpa only [Multiset.card_map, ← (IsAlgClosed.splits P).natDegree_eq_card_roots] using hdegree
  · rw [integral_shift_combination_eq_multiplier_energy] at henergy
    exact henergy
  · intro x hx
    have hpow : δ ^ n ≤ δ ^ P.natDegree := pow_le_pow_of_le_one hδ.le hδ1 hdegree
    have hprod : 0 ≤ (P.roots.map fun z => min 1 (τ * |x - ξ z|)).prod :=
      Multiset.prod_nonneg (by intro y hy; obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hy; positivity)
    have hh := (mul_le_mul_of_nonneg_right hpow hprod).trans (hξ x hx)
    simpa only [Multiset.map_map, Function.comp_def, P] using hh

/-- Small shift relations imply a weighted approximate spectrum of size at most
their order. The bound is uniform in the finite coefficient vector. -/
theorem exists_weighted_spectrum_of_shift_relations {N n : ℕ}
    (a : Fin (N + 1) → ℂ) {τ B : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ t : Set.Ioo (0 : ℝ) τ, ∃ c : Fin (n + 1) → ℂ,
      (∑ j, ‖c j‖ ^ 2) = 1 ∧
      (∫ q, ‖∑ j, c j * randomFourier a
        (angularTranslation N (j.val • (t.val : AddCircle (1 : ℝ))) q)‖ ^ 2
          ∂fourierMeasure N) ≤ B) :
    ∃ Λ : Multiset ℝ, Λ.card ≤ n ∧
      (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
        B / spectralEnergyCutoff n + B / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n) := by
  classical
  obtain ⟨T, _, hcard, houtside⟩ := exists_spectral_intervals_of_shift_relations a hτ hsmall
  let U : Finset ℝ := T.image Nat.cast
  have hU : U.card ≤ n := (Finset.card_image_le).trans hcard
  obtain ⟨t, c, Λ, _, hΛ, htotal, hinside⟩ := exists_weighted_shift_relation a U hU hτ hsmall
  refine ⟨Λ, hΛ, finite_spectral_weighted_energy_le a
    (fun k => ‖shiftMultiplier c (t : AddCircle (1 : ℝ)) k.val‖)
    (finiteIntervalUnion U (1 / (8 * ((n : ℝ) + 1) ^ 2) / τ))
    hτ.le (by positivity) (spectralEnergyCutoff_pos n) Λ n (fun _ => norm_nonneg _) ?_ ?_ htotal⟩
  · intro k hk
    have h := hinside k.val hk
    simpa only [spectralWeight, shiftMultiplier_eq_polynomial_eval,
      fourier_nat_eq_angularCharacter, mul_comm t] using h
  · have heq (k : Fin (N + 1)) :
        (k.val : ℝ) ∉ finiteIntervalUnion U (1 / (8 * ((n : ℝ) + 1) ^ 2) / τ) ↔
        ∀ m ∈ T, 1 / (8 * ((n : ℝ) + 1) ^ 2 * τ) < |(k.val : ℝ) - m| := by
      rw [not_mem_finiteIntervalUnion_iff, div_div]
      simp only [U, Finset.mem_image, forall_exists_index, and_imp]
      constructor
      · intro h m hm
        exact h _ m hm rfl
      · intro h x m hm hx
        subst x
        exact h m hm
    simpa only [heq] using houtside

/-- Restricted Fourier energy supplies a coefficient-uniform weighted spectrum.
The scale depends on the measurable set and the order parameter only. -/
theorem exists_weighted_spectrum_of_restricted_energy {N : ℕ}
    (E : Set (SignVector N × AddCircle (1 : ℝ))) (hE : MeasurableSet E)
    (hpos : 0 < (fourierMeasure N).real E) (m : ℕ) (hm : 1 ≤ m) :
    let n := shiftOrder ((fourierMeasure N).real E) m
    ∃ τ : ℝ, 0 < τ ∧ ∀ a : Fin (N + 1) → ℂ,
      ∃ Λ : Multiset ℝ, Λ.card ≤ n ∧
        (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
          (4 * ((n : ℝ) + 1) / (fourierMeasure N).real E *
            (∫ q in E, ‖randomFourier a q‖ ^ 2 ∂fourierMeasure N)) *
            (1 / spectralEnergyCutoff n + 1 / (1 / (8 * ((n : ℝ) + 1) ^ 2)) ^ (2 * n)) := by
  dsimp only
  obtain ⟨τ, hτ, hsmall⟩ := exists_quantitative_small_shifts E hE hpos m hm
  refine ⟨τ, hτ, fun a => ?_⟩
  obtain ⟨Λ, hΛ, hb⟩ := exists_weighted_spectrum_of_shift_relations a hτ
    (fun t => hsmall t.val t.property.1 t.property.2 a)
  refine ⟨Λ, hΛ, ?_⟩
  simpa only [mul_add, mul_one_div] using hb

end Erdos522.LogMoments

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.SpectralWeights
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Order.Interval.Set.Infinite

/-!
# Distinct perturbations of finite spectra

A finite spectrum, with its multiplicities, can be perturbed to distinct real
frequencies while changing any fixed finite weighted energy by an arbitrarily
small amount. The perturbation moves the indexed frequencies at distinct speeds;
only finitely many parameter values produce a collision.
-/

noncomputable section

open scoped BigOperators Classical

namespace Erdos522.LogMoments

/-- Arbitrarily small positive linear perturbations separate a finite tuple of
    real numbers, including a tuple with repeated entries. -/
theorem exists_injective_linear_perturbation {m : ℕ} (ξ : Fin m → ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ s ∈ Set.Ioo (0 : ℝ) η, Function.Injective (fun i => ξ i + s * (i.val : ℝ)) := by
  let collisions : Finset ℝ := Finset.univ.image fun q : Fin m × Fin m =>
    (ξ q.2 - ξ q.1) / ((q.1.val : ℝ) - (q.2.val : ℝ))
  obtain ⟨s, hs, havoid⟩ := (Set.Ioo_infinite hη).exists_notMem_finset collisions
  refine ⟨s, hs, ?_⟩
  intro i j hij
  by_contra hne
  have hval : (i.val : ℝ) ≠ (j.val : ℝ) := by
    intro heq
    apply hne
    apply Fin.ext
    exact_mod_cast heq
  have hslope : s = (ξ j - ξ i) / ((i.val : ℝ) - (j.val : ℝ)) := by
    apply (eq_div_iff (sub_ne_zero.mpr hval)).mpr
    nlinarith
  apply havoid
  exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, hslope.symm⟩

/-- The spectral weight of an indexed finite tuple is its finite product. -/
theorem spectralWeight_ofFn {m : ℕ} (τ x : ℝ) (ξ : Fin m → ℝ) :
    spectralWeight τ (List.ofFn ξ : Multiset ℝ) x =
      ∏ i, min 1 (τ * |x - ξ i|) := by
  simp only [spectralWeight, Multiset.map_coe, Multiset.prod_coe,
    ← List.ofFn_comp', List.prod_ofFn]

/-- Spectral weights depend continuously on a finite tuple of frequencies. -/
theorem continuous_spectralWeight_ofFn {X : Type*} [TopologicalSpace X]
    {m : ℕ} (τ x : ℝ) (ξ : Fin m → X → ℝ) (hξ : ∀ i, Continuous (ξ i)) :
    Continuous (fun y => spectralWeight τ (List.ofFn (fun i => ξ i y) : Multiset ℝ) x) := by
  simp only [spectralWeight_ofFn]
  exact continuous_finsetProd _ fun i _ =>
    continuous_const.min (continuous_const.mul ((continuous_const.sub (hξ i)).abs))

/-- A finite weighted energy is continuous under continuous motion of every
    spectral frequency. -/
theorem continuous_spectral_weighted_energy {X ι : Type*} [TopologicalSpace X]
    [Fintype ι] {m : ℕ} (a : ι → ℂ) (frequency : ι → ℝ) (τ : ℝ)
    (ξ : Fin m → X → ℝ) (hξ : ∀ i, Continuous (ξ i)) :
    Continuous (fun y => ∑ k, ‖a k‖ ^ 2 *
      (spectralWeight τ (List.ofFn (fun i => ξ i y) : Multiset ℝ) (frequency k)) ^ 2) := by
  exact continuous_finsetSum _ fun k _ => continuous_const.mul
    ((continuous_spectralWeight_ofFn τ (frequency k) ξ hξ).pow 2)

/-- Perturbing the frequencies to distinct values preserves their number and
    increases a prescribed finite weighted energy by less than any positive
    tolerance. The coefficient vector and its frequency locations are unchanged. -/
theorem exists_distinct_spectrum_energy_lt {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (frequency : ι → ℝ) (τ : ℝ) (Λ : Multiset ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : Multiset ℝ, Γ.Nodup ∧ Γ.card = Λ.card ∧
      (∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Γ (frequency k)) ^ 2) <
        (∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Λ (frequency k)) ^ 2) + ε := by
  let ξ : Fin Λ.toList.length → ℝ := Λ.toList.get
  let Γ : ℝ → Multiset ℝ := fun s => List.ofFn (fun i => ξ i + s * (i.val : ℝ))
  let energy : ℝ → ℝ := fun s =>
    ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ (Γ s) (frequency k)) ^ 2
  have hΓzero : Γ 0 = Λ := by
    simp only [Γ, zero_mul, add_zero, ξ, List.ofFn_get, Multiset.coe_toList]
  have hcontinuous : Continuous energy := by
    exact continuous_spectral_weighted_energy a frequency τ
      (fun i s => ξ i + s * (i.val : ℝ)) (by intro i; fun_prop)
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hcontinuous.continuousAt ε hε
  obtain ⟨s, hs, hinj⟩ := exists_injective_linear_perturbation ξ hη
  refine ⟨Γ s, Multiset.coe_nodup.mpr (List.nodup_ofFn_ofInjective hinj), ?_, ?_⟩
  · simp [Γ]
  · have hdist : dist s 0 < η := by simpa [Real.dist_eq, abs_of_pos hs.1] using hs.2
    have henergy := hclose hdist
    rw [Real.dist_eq] at henergy
    have hu := (abs_lt.mp henergy).2
    have henergyzero : energy 0 =
        ∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Λ (frequency k)) ^ 2 := by
      simp only [energy, hΓzero]
    change energy s < _
    rw [← henergyzero]
    linarith

/-- The non-strict form of the finite spectral perturbation bound. -/
theorem exists_distinct_spectrum_energy_le {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (frequency : ι → ℝ) (τ : ℝ) (Λ : Multiset ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : Multiset ℝ, Γ.Nodup ∧ Γ.card = Λ.card ∧
      (∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Γ (frequency k)) ^ 2) ≤
        (∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Λ (frequency k)) ^ 2) + ε := by
  obtain ⟨Γ, hΓ, hcard, henergy⟩ :=
    exists_distinct_spectrum_energy_lt a frequency τ Λ hε
  exact ⟨Γ, hΓ, hcard, henergy.le⟩

end Erdos522.LogMoments

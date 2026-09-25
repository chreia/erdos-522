/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.LogMoments.FourierApproximation

/-!
# Exponential approximation after spectral decomposition

Each non-residual spectral band has an approximant using its nearby frequencies.
Summing them preserves the original approximate spectrum; the residual band
and the local differential integrals give the total pointwise error.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- Differential forcing for the spectral band centered at the `j`th frequency. -/
def spectralBandForcing {N m : ℕ} (a : Fin (N + 1) → ℂ) (τ : ℝ)
    (ξ : Fin m → ℝ) (j : Fin m) : Fin (N + 1) → ℂ :=
  fun k => spectralBandCoefficients a τ ξ (some j) k *
    spectralDerivativeMultiplier (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)) k.val

/-- The integral remainder for one band on one interval. -/
def spectralBandIntegralError {N m : ℕ} (a : Fin (N + 1) → ℂ) (τ : ℝ)
    (ξ : Fin m → ℝ) (ω : SignVector N) (u v : ℝ) (j : Fin m) : ℝ :=
  (v - u) ^ ((spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card - 1) *
    ∫ t in u..v, ‖fourierPolynomial (spectralBandForcing a τ ξ j) ω (t : AddCircle (1 : ℝ))‖

/-- Spectral decomposition gives a local approximant in the full distinct spectrum. -/
theorem exists_spectral_band_approximation {N m : ℕ} (a : Fin (N + 1) → ℂ)
    {τ : ℝ} (hτ : 0 < τ) (ξ : Fin m → ℝ) (hξ : Function.Injective ξ)
    (ω : SignVector N) {u v : ℝ} (huv : u ≤ v) :
    ∃ p ∈ exponentialSpan (Set.range ξ), ∀ x ∈ Set.Icc u v,
      ‖fourierPolynomial a ω (x : AddCircle (1 : ℝ)) - p x‖ ≤
        ‖fourierPolynomial (spectralBandCoefficients a τ ξ none) ω (x : AddCircle (1 : ℝ))‖ +
          ∑ j, spectralBandIntegralError a τ ξ ω u v j := by
  classical
  let Ξ (j : Fin m) := (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).toList
  have hnodup (j : Fin m) : (Ξ j).Nodup := by
    apply Multiset.coe_nodup.mp
    change ((spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).toList : Multiset ℝ).Nodup
    rw [Multiset.coe_toList]
    exact spectralCluster_nodup τ (ξ j)
      (Multiset.coe_nodup.mpr (List.nodup_ofFn_ofInjective hξ))
  have hne (j : Fin m) : Ξ j ≠ [] := by
    have hc := (spectralCluster_ofFn_card_bounds hτ ξ j).1
    intro he
    have hz : (spectralCluster τ (ξ j) (List.ofFn ξ : Multiset ℝ)).card = 0 := by
      simpa only [Ξ, Multiset.length_toList, List.length_nil] using congrArg List.length he
    omega
  have hex (j : Fin m) := exists_local_fourier_approximation
    (spectralBandCoefficients a τ ξ (some j)) ω (Ξ j) (hnodup j) (hne j) huv
  choose p hp hbound using hex
  have hspan (j : Fin m) : p j ∈ exponentialSpan (Set.range ξ) := by
    apply exponentialSpan_mono (T := Set.range ξ) (fun z hz => ?_) (hp j)
    have hmem : z ∈ (List.ofFn ξ : Multiset ℝ) :=
      (Multiset.mem_filter.mp (Multiset.mem_toList.mp hz)).1
    simpa only [Multiset.mem_coe, List.mem_ofFn, Set.mem_range] using hmem
  refine ⟨∑ j, p j, Submodule.sum_mem _ (fun j _ => hspan j), ?_⟩
  intro x hx
  have hsum := sum_randomFourier_spectralBands a τ ξ (ω, (x : AddCircle (1 : ℝ)))
  rw [Fintype.sum_option] at hsum
  change fourierPolynomial (spectralBandCoefficients a τ ξ none) ω (x : AddCircle (1 : ℝ)) +
    (∑ j, fourierPolynomial (spectralBandCoefficients a τ ξ (some j)) ω
      (x : AddCircle (1 : ℝ))) = fourierPolynomial a ω (x : AddCircle (1 : ℝ)) at hsum
  rw [← hsum, Finset.sum_apply]
  rw [show ∀ z : ℂ, ∀ f g : Fin m → ℂ, z + (∑ j, f j) - ∑ j, g j =
    z + ∑ j, (f j - g j) by intro z f g; rw [Finset.sum_sub_distrib]; ring]
  apply (norm_add_le _ _).trans
  gcongr
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  convert! hbound j x hx using 1
  simp only [Ξ, spectralBandIntegralError,
    Multiset.length_toList, Multiset.coe_toList]
  rfl

end Erdos522.LogMoments

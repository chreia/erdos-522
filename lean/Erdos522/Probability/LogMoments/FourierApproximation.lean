/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialApproximation
import Erdos522.Probability.LogMoments.SpectralBands
import Erdos522.Probability.LogMoments.AveragedSpectrum

/-!
# Local exponential approximation of finite Fourier sums

The real lift of a finite Rademacher Fourier sum is an exponential sum for
each sign configuration. Its differential forcing therefore gives a local
approximant supported on any prescribed distinct list of frequencies.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522.LogMoments

/-- A real lift of the Fourier polynomial is a finite exponential sum. -/
theorem fourierPolynomial_real_eq_finiteExponentialSum {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ω : SignVector N) (x : ℝ) :
    fourierPolynomial a ω (x : AddCircle (1 : ℝ)) =
      finiteExponentialSum Finset.univ (fun k => sign (ω k) * a k)
        (fun k => (k.val : ℝ)) x := by
  simp only [fourierPolynomial_eq_sum, finiteExponentialSum, fourier_nat_eq_angularCharacter]

/-- The differential forcing of the real Fourier lift is exactly its spectral multiplier. -/
theorem finiteExponentialSum_spectral_multiplier {N : ℕ}
    (a : Fin (N + 1) → ℂ) (ω : SignVector N) (Ξ : List ℝ) (x : ℝ) :
    finiteExponentialSum Finset.univ
      (fun k => (sign (ω k) * a k) * (Ξ.map fun ξ => frequencyMultiplier ((k.val : ℝ) - ξ)).prod)
      (fun k => (k.val : ℝ)) x =
        fourierPolynomial (fun k => a k * spectralDerivativeMultiplier (Ξ : Multiset ℝ) k.val)
          ω (x : AddCircle (1 : ℝ)) := by
  rw [fourierPolynomial_real_eq_finiteExponentialSum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [spectralDerivativeMultiplier, Multiset.map_coe, Multiset.prod_coe]
  ring

/-- Local approximation with the exact integral remainder for each sign configuration. -/
theorem exists_local_fourier_approximation {N : ℕ} (a : Fin (N + 1) → ℂ)
    (ω : SignVector N) (Ξ : List ℝ) (hΞ : Ξ.Nodup) (hΞne : Ξ ≠ [])
    {u v : ℝ} (huv : u ≤ v) :
    ∃ p ∈ exponentialSpan {ξ | ξ ∈ Ξ}, ∀ x ∈ Set.Icc u v,
      ‖fourierPolynomial a ω (x : AddCircle (1 : ℝ)) - p x‖ ≤
        (v - u) ^ (Ξ.length - 1) *
          ∫ t in u..v, ‖fourierPolynomial
            (fun k => a k * spectralDerivativeMultiplier (Ξ : Multiset ℝ) k.val)
              ω (t : AddCircle (1 : ℝ))‖ := by
  obtain ⟨p, hp, hbound⟩ := exists_exponential_approximation Finset.univ
    (fun k => sign (ω k) * a k) (fun k => (k.val : ℝ)) Ξ hΞ hΞne huv
  refine ⟨p, hp, fun x hx => ?_⟩
  simpa only [finiteExponentialSum_spectral_multiplier,
    ← fourierPolynomial_real_eq_finiteExponentialSum] using hbound x hx

end Erdos522.LogMoments

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SteinhausLaw

/-!
# Logarithmic moments for Steinhaus Fourier polynomials

Unit-modulus coefficients have exact normalized Fourier energy. Central
symmetry transfers the uniform sign estimate to their original product law,
with no exceptional energy event.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Erdos522

/-- The energy event is certain for normalized coefficients of unit modulus. -/
theorem ae_steinhaus_coefficientEnergyEvent {N : ℕ}
    (c : Fin (N + 1) → ℂ) (hc : ∑ k, ‖c k‖ ^ 2 = 1) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure),
      a ∈ coefficientEnergyEvent c 1 := by
  filter_upwards [ae_pi_norm_steinhaus_eq_one] with a ha
  have he : ∑ k, ‖c k * a k‖ ^ 2 = 1 := by simp only [norm_mul, ha, mul_one, hc]
  simp only [coefficientEnergyEvent, mem_ofPred_eq, he]
  norm_num

/-- Normalized Steinhaus Fourier polynomials have coefficient-uniform
sixth-power logarithmic moments for every real moment order at least one. -/
theorem steinhaus_logarithmic_moments {N : ℕ}
    (c : Fin (N + 1) → ℂ) (hc : ∑ k, ‖c k‖ ^ 2 = 1) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun q => |Real.log ‖weightedCoefficientFourier c q‖| ^ p)
      ((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).prod AddCircle.haarAddCircle) ∧
    (∫ q, |Real.log ‖weightedCoefficientFourier c q‖| ^ p
      ∂((Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)).prod AddCircle.haarAddCircle)) ≤
        (LogMoments.amplitudeLogarithmicConstant 1 * p) ^ (6 * p) := by
  let μ := Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure)
  have he : ∀ᵐ q ∂μ.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      q ∈ coefficientEnergyEvent c 1 ×ˢ univ := by
    have hf : MeasurePreserving Prod.fst
        (μ.prod (AddCircle.haarAddCircle (T := (1 : ℝ)))) μ := measurePreserving_fst
    have h := hf.quasiMeasurePreserving.ae
      (ae_steinhaus_coefficientEnergyEvent c hc)
    filter_upwards [h] with q hq
    exact ⟨hq, mem_univ _⟩
  have hr := Measure.restrict_eq_self_of_ae_mem he
  dsimp only [μ] at hr
  have h := symmetric_event_restricted_logarithmic_moments
    (fun _ : Fin (N + 1) => steinhausMeasure) c 1 hp
  simpa only [IntegrableOn, hr] using h

/-- Exact angular energy for arbitrary coefficient vectors of unit modulus. -/
theorem integral_norm_sq_weightedCoefficientFourier {N : ℕ}
    (c a : Fin (N + 1) → ℂ) (ha : ∀ k, ‖a k‖ = 1) :
    (∫ θ : AddCircle (1 : ℝ), ‖weightedCoefficientFourier c (a, θ)‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ k, ‖c k‖ ^ 2 := by
  have h := LogMoments.integral_norm_sq_fourierPolynomial (fun k => c k * a k) (fun _ => true)
  simpa [weightedCoefficientFourier, LogMoments.fourierPolynomial_eq_sum,
    LogMoments.sign, norm_mul, ha] using h

/-- Normalized Steinhaus Fourier polynomials have unit angular energy almost surely. -/
theorem ae_steinhaus_angular_energy {N : ℕ}
    (c : Fin (N + 1) → ℂ) (hc : ∑ k, ‖c k‖ ^ 2 = 1) :
    ∀ᵐ a ∂Measure.pi (fun _ : Fin (N + 1) => steinhausMeasure),
      (∫ θ : AddCircle (1 : ℝ), ‖weightedCoefficientFourier c (a, θ)‖ ^ 2
        ∂AddCircle.haarAddCircle) = 1 := by
  filter_upwards [ae_pi_norm_steinhaus_eq_one] with a ha
  rw [integral_norm_sq_weightedCoefficientFourier c a ha, hc]

end Erdos522

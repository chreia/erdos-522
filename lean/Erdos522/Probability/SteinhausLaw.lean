/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricLogarithmicMoments
import Mathlib.MeasureTheory.Group.Integral

/-!
# The Steinhaus coefficient law

The first Fourier character sends normalized Haar measure on the additive
circle to the uniform law on the complex unit circle. A half turn gives
central symmetry, and every coefficient has modulus one.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- The uniform probability law on the complex unit circle. -/
def steinhausMeasure : Measure ℂ :=
  Measure.map (fourier 1 : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle

instance : IsProbabilityMeasure steinhausMeasure :=
  (Measure.isProbabilityMeasure_map_iff
    (fourier 1).continuous.measurable.aemeasurable).mpr inferInstance

/-- Translation by a half turn negates the first Fourier character. -/
theorem fourier_one_half_turn (θ : AddCircle (1 : ℝ)) :
    fourier 1 (θ + ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) = -fourier 1 θ := by
  simpa using fourier_add_half_inv_index (n := 1) (by norm_num) (by norm_num : (0 : ℝ) < 1) θ

instance : steinhausMeasure.IsNegInvariant where
  neg_eq_self := by
    change Measure.map (fun z : ℂ => -z) steinhausMeasure = steinhausMeasure
    have hm := measurePreserving_add_right (AddCircle.haarAddCircle (T := (1 : ℝ)))
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
    unfold steinhausMeasure
    rw [Measure.map_map measurable_neg (fourier 1).continuous.measurable]
    have heq : (fun z : ℂ => -z) ∘ (fourier 1 : AddCircle (1 : ℝ) → ℂ) =
        (fourier 1 : AddCircle (1 : ℝ) → ℂ) ∘
          (fun θ => θ + ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) := by
      funext θ
      exact (fourier_one_half_turn θ).symm
    rw [heq, ← Measure.map_map (fourier 1).continuous.measurable hm.measurable, hm.map_eq]

/-- A Steinhaus coefficient has modulus one almost surely. -/
theorem ae_norm_steinhaus_eq_one : ∀ᵐ z ∂steinhausMeasure, ‖z‖ = 1 := by
  rw [steinhausMeasure, ae_map_iff (fourier 1).continuous.measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  exact ae_of_all _ fun θ => by rw [fourier_one]; exact Circle.norm_coe _

/-- Steinhaus coefficients are integrable with mean zero. -/
theorem integrable_steinhaus : Integrable (fun z : ℂ => z) steinhausMeasure := by
  apply (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
  exact ae_norm_steinhaus_eq_one.mono (fun _ h => h.le)

theorem integral_steinhaus : (∫ z : ℂ, z ∂steinhausMeasure) = 0 := by
  have h := integral_neg_eq_self (fun z : ℂ => z) steinhausMeasure
  rw [integral_neg] at h
  linear_combination -(1 / 2 : ℂ) * h

/-- Every real absolute moment of a Steinhaus coefficient is one. -/
theorem integral_norm_rpow_steinhaus (p : ℝ) :
    (∫ z : ℂ, ‖z‖ ^ p ∂steinhausMeasure) = 1 := by
  calc
    _ = ∫ _z : ℂ, (1 : ℝ) ∂steinhausMeasure := integral_congr_ae
      (ae_norm_steinhaus_eq_one.mono (fun z hz => by rw [hz, Real.one_rpow]))
    _ = 1 := by simp

/-- Independent Steinhaus coefficients all have modulus one on one event. -/
theorem ae_pi_norm_steinhaus_eq_one {ι : Type*} [Fintype ι] :
    ∀ᵐ a ∂Measure.pi (fun _ : ι => steinhausMeasure), ∀ k, ‖a k‖ = 1 := by
  apply ae_all_iff.mpr
  intro k
  exact (measurePreserving_eval (fun _ : ι => steinhausMeasure) k).quasiMeasurePreserving.ae
    ae_norm_steinhaus_eq_one

end Erdos522

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Energy transfer from a local approximant

A squared-integral restriction bound for an approximating function transfers
to the original function with a controlled squared-error term.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

/-- A norm error gives a quadratic bound with the elementary constant two. -/
theorem norm_sq_le_twice_add_error {F : Type*} [NormedAddCommGroup F]
    (u v : F) {r : ℝ} (h : ‖u - v‖ ≤ r) : ‖u‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * r ^ 2 := by
  have hr : 0 ≤ r := (norm_nonneg _).trans h
  have hu : ‖u‖ ≤ ‖v‖ + r := by
    calc
      ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + r := by gcongr
  nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖v‖ - r)]

/-- An approximation and an `L²` restriction estimate transfer energy from
`E` to `J`, with explicit multiplier six. -/
theorem integral_norm_sq_le_of_local_approximation {Ω F : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup F] (μ : Measure Ω)
    (E J : Set Ω) (hE : MeasurableSet E) (hJ : MeasurableSet J)
    (hsub : E ⊆ J) (f p : Ω → F) (Φ : Ω → ℝ)
    {A c : ℝ} (hA : 1 ≤ A)
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) J μ)
    (hp : IntegrableOn (fun x => ‖p x‖ ^ 2) J μ)
    (hΦ : IntegrableOn (fun x => Φ x ^ 2) J μ)
    (happrox : ∀ x ∈ J, ‖f x - p x‖ ≤ c * Φ x)
    (hrestrict : (∫ x in J, ‖p x‖ ^ 2 ∂μ) ≤ A * ∫ x in E, ‖p x‖ ^ 2 ∂μ) :
    (∫ x in J, ‖f x‖ ^ 2 ∂μ) ≤
      6 * A * ((∫ x in E, ‖f x‖ ^ 2 ∂μ) + c ^ 2 * ∫ x in J, Φ x ^ 2 ∂μ) := by
  have hforward : (∫ x in J, ‖f x‖ ^ 2 ∂μ) ≤
      2 * (∫ x in J, ‖p x‖ ^ 2 ∂μ) + 2 * c ^ 2 * ∫ x in J, Φ x ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x in J, (2 * ‖p x‖ ^ 2 + (2 * c ^ 2) * Φ x ^ 2) ∂μ := by
        apply setIntegral_mono_on hf ((hp.const_mul 2).add (hΦ.const_mul _)) hJ
        intro x hx
        have h := norm_sq_le_twice_add_error (f x) (p x) (happrox x hx)
        simpa only [mul_pow, mul_assoc, Pi.add_apply] using h
      _ = _ := by rw [integral_add (hp.const_mul 2) (hΦ.const_mul _), integral_const_mul, integral_const_mul]
  have hreverse : (∫ x in E, ‖p x‖ ^ 2 ∂μ) ≤
      2 * (∫ x in E, ‖f x‖ ^ 2 ∂μ) + 2 * c ^ 2 * ∫ x in J, Φ x ^ 2 ∂μ := by
    have he : (∫ x in E, Φ x ^ 2 ∂μ) ≤ ∫ x in J, Φ x ^ 2 ∂μ :=
      setIntegral_mono_set hΦ (ae_of_all _ (fun x => sq_nonneg _)) (ae_of_all _ hsub)
    calc
      _ ≤ ∫ x in E, (2 * ‖f x‖ ^ 2 + (2 * c ^ 2) * Φ x ^ 2) ∂μ := by
        apply setIntegral_mono_on (hp.mono_set hsub)
          (((hf.mono_set hsub).const_mul 2).add ((hΦ.mono_set hsub).const_mul _)) hE
        intro x hx
        have h := norm_sq_le_twice_add_error (p x) (f x)
          (by simpa only [norm_sub_rev] using happrox x (hsub hx))
        simpa only [mul_pow, mul_assoc, Pi.add_apply] using h
      _ = 2 * (∫ x in E, ‖f x‖ ^ 2 ∂μ) + 2 * c ^ 2 * ∫ x in E, Φ x ^ 2 ∂μ := by
        rw [integral_add ((hf.mono_set hsub).const_mul 2) ((hΦ.mono_set hsub).const_mul _),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := by gcongr
  have herror : 0 ≤ c ^ 2 * ∫ x in J, Φ x ^ 2 ∂μ :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have henergy : 0 ≤ ∫ x in E, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hreverse (by linarith : 0 ≤ A)
  nlinarith

end Erdos522

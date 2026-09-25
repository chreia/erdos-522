/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.HarmonicGeometricRestriction
import Erdos522.Analysis.ExponentialAffineNormalization
import Erdos522.Analysis.GeometricEnergyRestriction
import Erdos522.Analysis.IntervalNormalization
import Erdos522.Probability.LogMoments.DistributionBound

/-!
# Measurable-set harmonic restriction

The geometric-mean inequality for harmonic exponential polynomials gives
the centered interval energy inequality by Jensen's inequality. Affine
normalization yields a constant uniform in the interval, the measurable
subset, and the real frequencies.
-/

noncomputable section
open MeasureTheory Set
namespace Erdos522

theorem one_le_harmonicRestrictionConstant : 1 ≤ harmonicRestrictionConstant :=
  (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2000)).trans
    exp_le_harmonicRestrictionConstant

/-- Harmonic exponential polynomials satisfy an energy restriction inequality
on every measurable part of the centered unit interval. -/
theorem harmonic_energy_restriction_centered {ι : Type*}
    (s : Finset ι) (c ζ : ι → ℂ) (hζ : ∀ j ∈ s, (ζ j).re = 0)
    (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hden : γ ≤ volume.real E) :
    (∫ x in Ico (-(1 / 2 : ℝ)) (1 / 2), ‖complexExponentialSum s c ζ (x : ℂ)‖ ^ 2) ≤
      (harmonicRestrictionConstant / γ) ^ (2 * s.card + 1) *
        ∫ x in E, ‖complexExponentialSum s c ζ (x : ℂ)‖ ^ 2 := by
  by_cases hzero : complexExponentialSum s c ζ = 0
  · simp [hzero]
  have hf : Continuous (fun x : ℝ => complexExponentialSum s c ζ (x : ℂ)) :=
    (analyticOnNhd_complexExponentialSum s c ζ).continuous.comp Complex.continuous_ofReal
  apply integral_norm_sq_le_of_geometric_restriction E hsub _ hf
    (integrableOn_log_norm_complexExponentialSum s c ζ hzero E hE hsub)
    (ae_complexExponentialSum_ne_zero s c ζ hzero E hE hsub)
    one_le_harmonicRestrictionConstant hγ hγ1 hden s.card
  intro x hx
  exact norm_complexExponentialSum_le_geometricMean_of_imaginary_spectrum
    s c ζ hζ E hE (by simpa only [neg_div] using hsub)
      (hγ.trans_le hden) x (abs_le.mpr ⟨hx.1, hx.2.le⟩)

/-- The coefficient-uniform harmonic `L²` restriction inequality, with the
same relative-density normalization on every uniform interval cell. -/
theorem harmonic_l2_restriction :
    LogMoments.HarmonicL2Restriction harmonicRestrictionConstant := by
  intro m ξ _hξ q hq γ hγ hγ1 i E hE hsub hden P hP
  obtain ⟨c, hc⟩ := exists_complexExponentialSum_of_mem_exponentialSpan ξ hP
  let u : ℝ := (i.val : ℝ) / q
  let v : ℝ := ((i.val : ℝ) + 1) / q
  have huv : u < v := (unitIntervalCell_endpoints hq i).2.1
  let a := (u + v) / 2
  let l := v - u
  let A := realAffineEquiv a l (sub_pos.mpr huv).ne'
  let E' := A ⁻¹' E
  let ζ : Fin m → ℂ := fun j => frequencyMultiplier (ξ j)
  let c' : Fin m → ℂ := fun j => c j * Complex.exp (ζ j * (a : ℂ))
  let ζ' : Fin m → ℂ := fun j => ζ j * (l : ℂ)
  have hE' : MeasurableSet E' := hE.preimage A.measurable
  have hsub' : E' ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
    preimage_subset_centered_interval huv hsub
  have hden' : γ ≤ volume.real E' :=
    le_volumeReal_preimage_interval_center huv E hE hden
  have him : ∀ j ∈ (Finset.univ : Finset (Fin m)), (ζ' j).re = 0 := by
    intro j _
    exact purelyImaginary_spectrum_affine ζ (fun j => frequencyMultiplier_re (ξ j)) l j
  have hPaffine (x : ℝ) : P (a + l * x) = complexExponentialSum Finset.univ c' ζ' x := by
    rw [hc, Complex.ofReal_add, Complex.ofReal_mul, complexExponentialSum_affine]
  have hnormalized := harmonic_energy_restriction_centered Finset.univ c' ζ'
    him E' hE' hsub' hγ hγ1 hden'
  have hscaled : (∫ x in Ico (-(1 / 2 : ℝ)) (1 / 2), ‖P (a + l * x)‖ ^ 2) ≤
      (harmonicRestrictionConstant / γ) ^ (2 * m + 1) *
        ∫ x in E', ‖P (a + l * x)‖ ^ 2 := by
    simpa only [hPaffine, Finset.card_univ, Fintype.card_fin] using hnormalized
  exact integral_Ico_le_of_affine_restriction huv E (fun x => ‖P x‖ ^ 2) hscaled

end Erdos522

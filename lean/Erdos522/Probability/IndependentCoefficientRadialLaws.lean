/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.SymmetricCoefficientLaws
import Erdos522.Probability.GaussianRadialProfile
import Erdos522.Probability.SteinhausRadialProfile
import Erdos522.Probability.RadialProfile
import Erdos522.Probability.RademacherZeroDistribution
import Erdos522.Probability.CircularGaussianRadialProfile

/-!
# Radial laws on arbitrary probability spaces

Independence and a common coefficient law identify the distribution of the
entire coefficient process with the infinite product law. Almost-sure radial
statements therefore hold for a nested iid sequence on any probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace Erdos522

/-- An almost-sure property of the infinite product law transfers to every iid
process with that coefficient law. No measurability of the property is needed. -/
theorem ae_iid_sequence_property {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {μ : Measure α} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → α}
    (hξ : ∀ k, HasLaw (ξ k) μ P) (hind : iIndepFun ξ P)
    {Q : (ℕ → α) → Prop} (hQ : ∀ᵐ a ∂Measure.infinitePi (fun _ : ℕ => μ), Q a) :
    ∀ᵐ ω ∂P, Q (fun k => ξ k ω) := by
  have hprocess := hind.hasLaw_infinitePi hξ
    (aemeasurable_pi_iff.mpr (fun k => (hξ k).aemeasurable))
  rw [← hprocess.map_eq] at hQ
  exact ae_of_ae_map hprocess.aemeasurable hQ

/-- The Erdős strong law for independent fair signs on an arbitrary probability space. -/
theorem erdos_522_of_independent_coins {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ℕ → Ω → Bool}
    (hξ : ∀ k, HasLaw (ξ k) (PMF.uniformOfFintype Bool).toMeasure P)
    (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (closedZeroCount (polynomialPrefix (fun k => LogMoments.sign (ξ k ω)) (fun _ => 1) N) 1 : ℝ) / N)
      atTop (𝓝 (1 / 2 : ℝ)) :=
  ae_iid_sequence_property hξ hind erdos_522

/-- The compact-uniform radial profile for independent fair signs on any probability space. -/
theorem iid_rademacher_radial_profile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ℕ → Ω → Bool}
    (hξ : ∀ k, HasLaw (ξ k) (PMF.uniformOfFintype Bool).toMeasure P)
    (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => LogMoments.sign (ξ k ω)) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s :=
  ae_iid_sequence_property hξ hind radial_profile_compact_uniform_prefixes

/-- The compact-uniform radial profile for nontrivial bounded centrally symmetric iid coefficients. -/
theorem iid_bounded_symmetric_radial_profile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    {B : ℝ} (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hzero : μ {0} < 1)
    {ξ : ℕ → Ω → ℂ} (hξ : ∀ k, HasLaw (ξ k) μ P) (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => ξ k ω) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s :=
  ae_iid_sequence_property hξ hind
    (bounded_symmetric_radial_profile_compact_uniform_of_nontrivial μ hbound hzero)

/-- The strong law for nontrivial bounded centrally symmetric iid coefficients. -/
theorem iid_bounded_symmetric_zero_distribution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (μ : Measure ℂ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    {B : ℝ} (hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (hzero : μ {0} < 1)
    {ξ : ℕ → Ω → ℂ} (hξ : ∀ k, HasLaw (ξ k) μ P) (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (closedZeroCount (polynomialPrefix (fun k => ξ k ω) (fun _ => 1) N) 1 : ℝ) / N)
      atTop (𝓝 (1 / 2 : ℝ)) :=
  ae_iid_sequence_property hξ hind (bounded_symmetric_zero_distribution_of_nontrivial μ hbound hzero)

/-- The compact-uniform radial profile for iid standard real Gaussian coefficients. -/
theorem iid_gaussian_radial_profile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ℕ → Ω → ℝ}
    (hξ : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P) (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => (ξ k ω : ℂ)) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s :=
  ae_iid_sequence_property hξ hind gaussian_radial_profile_compact_uniform_prefixes

/-- The compact-uniform radial profile for iid Steinhaus coefficients. -/
theorem iid_steinhaus_radial_profile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ℕ → Ω → ℂ}
    (hξ : ∀ k, HasLaw (ξ k) steinhausMeasure P) (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => ξ k ω) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s :=
  ae_iid_sequence_property hξ hind steinhaus_radial_profile_compact_uniform_prefixes

/-- The compact-uniform radial profile for iid circular complex Gaussian coefficients. -/
theorem iid_circularGaussian_radial_profile {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ξ : ℕ → Ω → ℂ}
    (hξ : ∀ k, HasLaw (ξ k) circularComplexGaussian P) (hind : iIndepFun ξ P) :
    ∀ᵐ ω ∂P, ∀ s : Set ℝ, IsCompact s →
      TendstoUniformlyOn (fun N : ℕ => fun x : ℝ =>
        (closedZeroCount (polynomialPrefix (fun k => ξ k ω) (fun _ => 1) N)
          (1 + x / N) : ℝ) / N) kacRadialProfile atTop s :=
  ae_iid_sequence_property hξ hind circularGaussian_radial_profile_compact_uniform_prefixes

end Erdos522

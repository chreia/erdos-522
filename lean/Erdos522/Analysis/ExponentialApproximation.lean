/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialSpan
import Erdos522.Analysis.IteratedOscillatoryIntegration

/-!
# Exponential approximation by integrating factors

Subtracting the iterated particular solution from a character leaves an
exponential polynomial supported on the integrating frequencies. Distinctness
prevents resonances between successive integrating factors.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Erdos522

/-- A finite complex exponential sum with real frequencies. -/
def finiteExponentialSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ)
    (x : ℝ) : ℂ := ∑ k ∈ s, c k * angularCharacter (ν k * x)

theorem continuous_finiteExponentialSum {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ) : Continuous (finiteExponentialSum s c ν) :=
  continuous_finsetSum s (fun k _ => continuous_const.mul (continuous_angularCharacter_mul (ν k)))

/-- The remainder of one integrating factor has its integrating frequency. -/
theorem character_sub_primitive_mem_exponentialSpan (ξ η a : ℝ) :
    (fun x => angularCharacter (η * x) - frequencyMultiplier (η - ξ) *
      oscillatoryPrimitive ξ a (fun t => angularCharacter (η * t)) x) ∈
        exponentialSpan {ξ} := by
  have h := (exponentialSpan {ξ}).smul_mem
    (angularCharacter (-ξ * a) * angularCharacter (η * a))
    (character_mem_exponentialSpan (show ξ ∈ ({ξ} : Set ℝ) by simp))
  convert h using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [frequencyMultiplier_mul_primitive_character]
  have hphase : angularCharacter (ξ * (x - a)) =
      angularCharacter (ξ * x) * angularCharacter (-ξ * a) := by
    rw [← angularCharacter_add]
    congr 1
    ring
  rw [hphase]
  ring

/-- The remainder after finitely many distinct integrating factors belongs to
their exponential span, even when the forcing frequency is one of them. -/
theorem character_sub_iteratedPrimitive_mem_exponentialSpan
    (Ξ : List ℝ) (hΞ : Ξ.Nodup) (η a : ℝ) :
    (fun x => angularCharacter (η * x) -
      (Ξ.map fun ξ => frequencyMultiplier (η - ξ)).prod *
        iteratedOscillatoryPrimitive Ξ a (fun t => angularCharacter (η * t)) x) ∈
          exponentialSpan {ξ | ξ ∈ Ξ} := by
  induction Ξ with
  | nil =>
      simp only [List.map_nil, List.prod_nil, iteratedOscillatoryPrimitive, one_mul, sub_self,
        List.not_mem_nil, Set.ofPred_false]
      exact (exponentialSpan (∅ : Set ℝ)).zero_mem
  | cons ξ Ξ ih =>
      have hnodup := List.nodup_cons.mp hΞ
      have htail := ih hnodup.2
      let f : ℝ → ℂ := fun x => angularCharacter (η * x)
      let g := iteratedOscillatoryPrimitive Ξ a f
      let D := (Ξ.map fun ζ => frequencyMultiplier (η - ζ)).prod
      let r : ℝ → ℂ := f - D • g
      have hr : r ∈ exponentialSpan {ζ | ζ ∈ Ξ} := htail
      have hprim := oscillatoryPrimitive_mem_exponentialSpan hr ξ a hnodup.1
      have hfirst := exponentialSpan_mono
        (show ({ξ} : Set ℝ) ⊆ insert ξ {ζ | ζ ∈ Ξ} by simp)
        (character_sub_primitive_mem_exponentialSpan ξ η a)
      have hsum := (exponentialSpan (insert ξ {ζ | ζ ∈ Ξ})).add_mem hfirst
        ((exponentialSpan (insert ξ {ζ | ζ ∈ Ξ})).smul_mem (frequencyMultiplier (η - ξ)) hprim)
      have hfc : Continuous f := continuous_angularCharacter_mul η
      have hgc : Continuous g := continuous_iteratedOscillatoryPrimitive Ξ a hfc
      have hdecomp : oscillatoryPrimitive ξ a r =
          oscillatoryPrimitive ξ a f - D • oscillatoryPrimitive ξ a g := by
        rw [show r = f - D • g from rfl,
          oscillatoryPrimitive_sub ξ a hfc (hgc.const_smul D)]
        congr 1
        funext x
        exact oscillatoryPrimitive_const_mul ξ a D g x
      have hset : {ζ | ζ ∈ ξ :: Ξ} = insert ξ {ζ | ζ ∈ Ξ} := by ext ζ; simp
      rw [hset]
      convert hsum using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdecomp, Pi.sub_apply,
        List.map_cons, List.prod_cons, iteratedOscillatoryPrimitive]
      change f x - (frequencyMultiplier (η - ξ) * D) * oscillatoryPrimitive ξ a g x =
        (f x - frequencyMultiplier (η - ξ) * oscillatoryPrimitive ξ a f x) +
          frequencyMultiplier (η - ξ) *
            (oscillatoryPrimitive ξ a f x - D * oscillatoryPrimitive ξ a g x)
      ring

/-- Removing the iterated particular solution leaves only the prescribed frequencies. -/
theorem finiteExponentialSum_sub_iteratedPrimitive_mem {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (Ξ : List ℝ) (hΞ : Ξ.Nodup) (a : ℝ) :
    (finiteExponentialSum s c ν - iteratedOscillatoryPrimitive Ξ a
      (finiteExponentialSum s (fun k => c k *
        (Ξ.map fun ξ => frequencyMultiplier (ν k - ξ)).prod) ν)) ∈
          exponentialSpan {ξ | ξ ∈ Ξ} := by
  let e : ι → ℝ → ℂ := fun k x => angularCharacter (ν k * x)
  let D : ι → ℂ := fun k => (Ξ.map fun ξ => frequencyMultiplier (ν k - ξ)).prod
  have hmem : (∑ k ∈ s, c k • (e k - D k • iteratedOscillatoryPrimitive Ξ a (e k))) ∈
      exponentialSpan {ξ | ξ ∈ Ξ} := by
    apply Submodule.sum_mem
    intro k _
    exact (exponentialSpan {ξ | ξ ∈ Ξ}).smul_mem (c k)
      (character_sub_iteratedPrimitive_mem_exponentialSpan Ξ hΞ (ν k) a)
  have hforcing : finiteExponentialSum s (fun k => c k * D k) ν =
      ∑ k ∈ s, (c k * D k) • e k := by
    funext x
    simp [finiteExponentialSum, e]
  change (finiteExponentialSum s c ν -
    iteratedOscillatoryPrimitive Ξ a (finiteExponentialSum s (fun k => c k * D k) ν)) ∈ _
  rw [hforcing, iteratedOscillatoryPrimitive_sum s Ξ a _
    (fun k _ => (continuous_angularCharacter_mul (ν k)).const_smul (c k * D k))]
  simp_rw [iteratedOscillatoryPrimitive_smul]
  convert hmem using 1
  funext x
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    finiteExponentialSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change c k * e k x - (c k * D k) * iteratedOscillatoryPrimitive Ξ a (e k) x =
    c k * (e k x - D k * iteratedOscillatoryPrimitive Ξ a (e k) x)
  ring

/-- A finite exponential sum admits a prescribed-frequency approximant whose
uniform error is controlled by the integral of its differential forcing. -/
theorem exists_exponential_approximation {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (Ξ : List ℝ)
    (hΞ : Ξ.Nodup) (hΞne : Ξ ≠ []) {a b : ℝ} (hab : a ≤ b) :
    ∃ p ∈ exponentialSpan {ξ | ξ ∈ Ξ}, ∀ x ∈ Set.Icc a b,
      ‖finiteExponentialSum s c ν x - p x‖ ≤
        (b - a) ^ (Ξ.length - 1) *
          ∫ t in a..b, ‖finiteExponentialSum s (fun k => c k *
            (Ξ.map fun ξ => frequencyMultiplier (ν k - ξ)).prod) ν t‖ := by
  let h := finiteExponentialSum s (fun k => c k *
    (Ξ.map fun ξ => frequencyMultiplier (ν k - ξ)).prod) ν
  refine ⟨finiteExponentialSum s c ν - iteratedOscillatoryPrimitive Ξ a h,
    finiteExponentialSum_sub_iteratedPrimitive_mem s c ν Ξ hΞ a, ?_⟩
  intro x hx
  simp only [Pi.sub_apply, sub_sub_cancel]
  exact norm_iteratedOscillatoryPrimitive_integral_le Ξ hΞne hab
    (continuous_finiteExponentialSum s _ ν) x hx

end Erdos522

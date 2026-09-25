/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.ExponentialPrimitives

/-!
# Iterated integrating factors

Successive zero-initial-value inverses of first-order frequency operators
obey an interval-length bound independent of all the frequencies.
-/

noncomputable section
open MeasureTheory
namespace Erdos522

/-- Successive integrating-factor primitives, in list order. -/
def iteratedOscillatoryPrimitive : List ℝ → ℝ → (ℝ → ℂ) → ℝ → ℂ
  | [], _, h => h
  | ξ :: Ξ, a, h => oscillatoryPrimitive ξ a (iteratedOscillatoryPrimitive Ξ a h)

@[simp] theorem iteratedOscillatoryPrimitive_zero (Ξ : List ℝ) (a : ℝ) :
    iteratedOscillatoryPrimitive Ξ a 0 = 0 := by
  induction Ξ with
  | nil => rfl
  | cons ξ Ξ ih => simp only [iteratedOscillatoryPrimitive, ih, oscillatoryPrimitive_zero]

/-- Constants commute with all the integrating factors. -/
theorem iteratedOscillatoryPrimitive_smul (Ξ : List ℝ) (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    iteratedOscillatoryPrimitive Ξ a (c • f) = c • iteratedOscillatoryPrimitive Ξ a f := by
  induction Ξ with
  | nil => rfl
  | cons ξ Ξ ih =>
      simp only [iteratedOscillatoryPrimitive, ih]
      funext x
      exact oscillatoryPrimitive_const_mul ξ a c _ x

/-- Iterated primitives preserve continuity. -/
theorem continuous_iteratedOscillatoryPrimitive (Ξ : List ℝ) (a : ℝ)
    {h : ℝ → ℂ} (hh : Continuous h) :
    Continuous (iteratedOscillatoryPrimitive Ξ a h) := by
  induction Ξ with
  | nil => exact hh
  | cons ξ Ξ ih =>
      exact (show Differentiable ℝ (oscillatoryPrimitive ξ a (iteratedOscillatoryPrimitive Ξ a h)) from
        fun x => (hasDerivAt_oscillatoryPrimitive ξ a ih x).differentiableAt).continuous

/-- Iterated integration is additive on continuous functions. -/
theorem iteratedOscillatoryPrimitive_add (Ξ : List ℝ) (a : ℝ)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    iteratedOscillatoryPrimitive Ξ a (f + g) =
      iteratedOscillatoryPrimitive Ξ a f + iteratedOscillatoryPrimitive Ξ a g := by
  induction Ξ with
  | nil => rfl
  | cons ξ Ξ ih =>
      simp only [iteratedOscillatoryPrimitive, ih]
      exact oscillatoryPrimitive_add ξ a (continuous_iteratedOscillatoryPrimitive Ξ a hf)
        (continuous_iteratedOscillatoryPrimitive Ξ a hg)

/-- Finite continuous sums can be integrated term by term. -/
theorem iteratedOscillatoryPrimitive_sum {ι : Type*} (s : Finset ι)
    (Ξ : List ℝ) (a : ℝ) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) :
    iteratedOscillatoryPrimitive Ξ a (∑ i ∈ s, f i) =
      ∑ i ∈ s, iteratedOscillatoryPrimitive Ξ a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs : Continuous (∑ j ∈ s, f j) := by
        convert continuous_finsetSum s (fun j hj => hf j (Finset.mem_insert_of_mem hj)) using 1
        funext x
        simp
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        iteratedOscillatoryPrimitive_add Ξ a (hf i (Finset.mem_insert_self _ _)) hs,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- A uniform forcing bound gains one interval-length factor at each integration. -/
theorem norm_iteratedOscillatoryPrimitive_le (Ξ : List ℝ) {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) {h : ℝ → ℂ} (hh : Continuous h)
    (hbound : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedOscillatoryPrimitive Ξ a h x‖ ≤ (b - a) ^ Ξ.length * M := by
  induction Ξ with
  | nil => simpa only [iteratedOscillatoryPrimitive, List.length_nil, pow_zero, one_mul] using hbound
  | cons ξ Ξ ih =>
      intro x hx
      have hcont := continuous_iteratedOscillatoryPrimitive Ξ a hh
      have hcoef : 0 ≤ (b - a) ^ Ξ.length * M := mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hM
      calc
        _ ≤ ∫ t in a..x, ‖iteratedOscillatoryPrimitive Ξ a h t‖ :=
          norm_oscillatoryPrimitive_le ξ hx.1 _
        _ ≤ ∫ _t in a..x, (b - a) ^ Ξ.length * M :=
          intervalIntegral.integral_mono_on hx.1 (hcont.norm.intervalIntegrable a x)
            (intervalIntegrable_const) (fun t ht => ih t ⟨ht.1, ht.2.trans hx.2⟩)
        _ = (x - a) * ((b - a) ^ Ξ.length * M) := by simp; ring
        _ ≤ (b - a) * ((b - a) ^ Ξ.length * M) :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hcoef
        _ = (b - a) ^ (ξ :: Ξ).length * M := by rw [List.length_cons, pow_succ]; ring

/-- Concatenation composes the corresponding integration operators. -/
theorem iteratedOscillatoryPrimitive_append (Ξ Γ : List ℝ) (a : ℝ) (h : ℝ → ℂ) :
    iteratedOscillatoryPrimitive (Ξ ++ Γ) a h =
      iteratedOscillatoryPrimitive Ξ a (iteratedOscillatoryPrimitive Γ a h) := by
  induction Ξ with
  | nil => rfl
  | cons ξ Ξ ih => simp only [List.cons_append, iteratedOscillatoryPrimitive, ih]

/-- An integral forcing bound yields the `length - 1` power for a nonempty sequence. -/
theorem norm_iteratedOscillatoryPrimitive_append_singleton_le
    (Ξ : List ℝ) (ξ : ℝ) {a b : ℝ} (hab : a ≤ b)
    {h : ℝ → ℂ} (hh : Continuous h) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedOscillatoryPrimitive (Ξ ++ [ξ]) a h x‖ ≤
        (b - a) ^ Ξ.length * ∫ t in a..b, ‖h t‖ := by
  have hI : 0 ≤ ∫ t in a..b, ‖h t‖ :=
    intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
  rw [iteratedOscillatoryPrimitive_append]
  apply norm_iteratedOscillatoryPrimitive_le Ξ hab hI
    (continuous_iteratedOscillatoryPrimitive [ξ] a hh)
  intro x hx
  exact (norm_oscillatoryPrimitive_le ξ hx.1 h).trans
    (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hh.norm.intervalIntegrable a b))

/-- The integral remainder bound for any nonempty list of frequencies. -/
theorem norm_iteratedOscillatoryPrimitive_integral_le (Ξ : List ℝ) (hΞ : Ξ ≠ [])
    {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℂ} (hh : Continuous h) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedOscillatoryPrimitive Ξ a h x‖ ≤
        (b - a) ^ (Ξ.length - 1) * ∫ t in a..b, ‖h t‖ := by
  induction Ξ using List.reverseRecOn with
  | nil => exact (hΞ rfl).elim
  | append_singleton Ξ ξ _ih =>
      simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel] using
        norm_iteratedOscillatoryPrimitive_append_singleton_le Ξ ξ hab hh

end Erdos522

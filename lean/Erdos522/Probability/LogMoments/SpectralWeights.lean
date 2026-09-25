/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Analysis.PolynomialRootPhases

/-!
# Clipped spectral weights and finite energy bounds

A finite multiset of real frequencies defines a product of clipped distances.
Splitting the coefficient energy into the covered frequencies and their
complement combines a polynomial multiplier bound with a residual-energy bound.
-/

noncomputable section

open scoped BigOperators Classical

namespace Erdos522.LogMoments

/-- The product of the clipped distances to a multiset of spectral frequencies. -/
def spectralWeight (τ : ℝ) (Λ : Multiset ℝ) (x : ℝ) : ℝ :=
  (Λ.map fun ξ => min 1 (τ * |x - ξ|)).prod

@[simp] theorem spectralWeight_zero (τ x : ℝ) : spectralWeight τ 0 x = 1 := by
  simp [spectralWeight]

@[simp] theorem spectralWeight_cons (τ ξ x : ℝ) (Λ : Multiset ℝ) :
    spectralWeight τ (ξ ::ₘ Λ) x = min 1 (τ * |x - ξ|) * spectralWeight τ Λ x := by
  simp [spectralWeight]

/-- Concatenating frequency multisets multiplies their weights, preserving multiplicities. -/
theorem spectralWeight_add (τ x : ℝ) (Λ Γ : Multiset ℝ) :
    spectralWeight τ (Λ + Γ) x = spectralWeight τ Λ x * spectralWeight τ Γ x := by
  simp [spectralWeight]

/-- Every clipped spectral weight lies in the closed unit interval. -/
theorem spectralWeight_mem_Icc {τ : ℝ} (hτ : 0 ≤ τ) (Λ : Multiset ℝ) (x : ℝ) :
    spectralWeight τ Λ x ∈ Set.Icc (0 : ℝ) 1 := by
  induction Λ using Multiset.induction_on with
  | empty => simp
  | cons ξ Λ ih =>
      rw [spectralWeight_cons]
      have hfactor : 0 ≤ min 1 (τ * |x - ξ|) := le_min (by norm_num) (by positivity)
      refine ⟨mul_nonneg hfactor ih.1, ?_⟩
      calc
        _ ≤ 1 * 1 := mul_le_mul (min_le_left _ _) ih.2 ih.1 (by norm_num)
        _ = 1 := one_mul _

theorem spectralWeight_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (Λ : Multiset ℝ) (x : ℝ) :
    0 ≤ spectralWeight τ Λ x := (spectralWeight_mem_Icc hτ Λ x).1

theorem spectralWeight_le_one {τ : ℝ} (hτ : 0 ≤ τ) (Λ : Multiset ℝ) (x : ℝ) :
    spectralWeight τ Λ x ≤ 1 := (spectralWeight_mem_Icc hτ Λ x).2

/-- The spectral weight is continuous in the frequency variable. -/
theorem continuous_spectralWeight (τ : ℝ) (Λ : Multiset ℝ) :
    Continuous (spectralWeight τ Λ) := by
  induction Λ using Multiset.induction_on with
  | empty =>
      change Continuous (fun x => spectralWeight τ 0 x)
      simp only [spectralWeight_zero]
      exact continuous_const
  | cons ξ Λ ih =>
      have hfactor : Continuous (fun x : ℝ => min 1 (τ * |x - ξ|)) := by fun_prop
      change Continuous (fun x => spectralWeight τ (ξ ::ₘ Λ) x)
      simp only [spectralWeight_cons]
      exact hfactor.mul ih

/-- Mapping a multiset of labels to frequencies gives exactly the corresponding
    product over the original labels. -/
theorem spectralWeight_map {α : Type*} (τ x : ℝ) (s : Multiset α) (ξ : α → ℝ) :
    spectralWeight τ (s.map ξ) x = (s.map fun z => min 1 (τ * |x - ξ z|)).prod := by
  simp only [spectralWeight, Multiset.map_map, Function.comp_def]

/-- Polynomial root multiplicities are retained by the spectral-weight product. -/
theorem spectralWeight_roots (τ x : ℝ) (P : Polynomial ℂ) (ξ : ℂ → ℝ) :
    spectralWeight τ (P.roots.map ξ) x =
      (P.roots.map fun z => min 1 (τ * |x - ξ z|)).prod :=
  spectralWeight_map τ x P.roots ξ

/-- A pointwise multiplier bound on one part of a finite index set and an energy
    bound on its complement give the exact weighted-energy estimate. -/
theorem sum_weighted_sq_le_of_partition {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (w b : ι → ℝ) (covered : ι → Prop)
    (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∀ k, w k ≤ 1) (hb : ∀ k, 0 ≤ b k)
    {δ γ B : ℝ} (hδ : 0 < δ) (_hγ : 0 < γ) (n : ℕ)
    (hinside : ∀ k, covered k → δ ^ n * w k ≤ b k)
    (houtside : (∑ k ∈ Finset.univ.filter (fun k => ¬ covered k), ‖a k‖ ^ 2) ≤ B / γ)
    (htotal : (∑ k, ‖a k‖ ^ 2 * (b k) ^ 2) ≤ B) :
    (∑ k, ‖a k‖ ^ 2 * (w k) ^ 2) ≤ B / γ + B / δ ^ (2 * n) := by
  classical
  have hδn : 0 < δ ^ n := pow_pos hδ _
  have hδ2n : 0 < δ ^ (2 * n) := pow_pos hδ _
  have hpower : δ ^ (2 * n) = (δ ^ n) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have hinsideEnergy :
      (∑ k ∈ Finset.univ.filter covered, ‖a k‖ ^ 2 * (w k) ^ 2) ≤ B / δ ^ (2 * n) := by
    apply (le_div_iff₀ hδ2n).mpr
    rw [mul_comm]
    calc
      _ = ∑ k ∈ Finset.univ.filter covered, ‖a k‖ ^ 2 * (δ ^ n * w k) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [hpower]
        ring
      _ ≤ ∑ k ∈ Finset.univ.filter covered, ‖a k‖ ^ 2 * (b k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (sq_le_sq₀ (mul_nonneg hδn.le (hw0 k)) (hb k)).mpr
          (hinside k (Finset.mem_filter.mp hk).2)
      _ ≤ ∑ k, ‖a k‖ ^ 2 * (b k) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ B := htotal
  have houtsideEnergy :
      (∑ k ∈ Finset.univ.filter (fun k => ¬ covered k), ‖a k‖ ^ 2 * (w k) ^ 2) ≤ B / γ := by
    calc
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k => ¬ covered k), ‖a k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hsquare : (w k) ^ 2 ≤ 1 := by nlinarith [hw0 k, hw1 k]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare (sq_nonneg ‖a k‖)
      _ ≤ B / γ := houtside
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ covered
    (fun k => ‖a k‖ ^ 2 * (w k) ^ 2)
  rw [← hsplit]
  linarith

/-- Spectral weights inherit the exact covered-frequency energy estimate. -/
theorem sum_spectralWeight_sq_le_of_partition {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (frequency b : ι → ℝ) (covered : ι → Prop)
    {τ δ γ B : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) (hγ : 0 < γ)
    (Λ : Multiset ℝ) (n : ℕ) (hb : ∀ k, 0 ≤ b k)
    (hinside : ∀ k, covered k → δ ^ n * spectralWeight τ Λ (frequency k) ≤ b k)
    (houtside : (∑ k ∈ Finset.univ.filter (fun k => ¬ covered k), ‖a k‖ ^ 2) ≤ B / γ)
    (htotal : (∑ k, ‖a k‖ ^ 2 * (b k) ^ 2) ≤ B) :
    (∑ k, ‖a k‖ ^ 2 * (spectralWeight τ Λ (frequency k)) ^ 2) ≤
      B / γ + B / δ ^ (2 * n) :=
  sum_weighted_sq_le_of_partition a (fun k => spectralWeight τ Λ (frequency k)) b covered
    (fun k => spectralWeight_nonneg hτ Λ (frequency k))
    (fun k => spectralWeight_le_one hτ Λ (frequency k)) hb hδ hγ n hinside houtside htotal

/-- The finite Fourier-frequency specialization of the weighted-energy estimate. -/
theorem finite_spectral_weighted_energy_le {N : ℕ}
    (a : Fin (N + 1) → ℂ) (b : Fin (N + 1) → ℝ) (S : Set ℝ)
    {τ δ γ B : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) (hγ : 0 < γ)
    (Λ : Multiset ℝ) (n : ℕ) (hb : ∀ k, 0 ≤ b k)
    (hinside : ∀ k : Fin (N + 1), (k.val : ℝ) ∈ S →
      δ ^ n * spectralWeight τ Λ k.val ≤ b k)
    (houtside : (∑ k ∈ Finset.univ.filter (fun k : Fin (N + 1) => (k.val : ℝ) ∉ S),
      ‖a k‖ ^ 2) ≤ B / γ)
    (htotal : (∑ k, ‖a k‖ ^ 2 * (b k) ^ 2) ≤ B) :
    (∑ k : Fin (N + 1), ‖a k‖ ^ 2 * (spectralWeight τ Λ k.val) ^ 2) ≤
      B / γ + B / δ ^ (2 * n) :=
  sum_spectralWeight_sq_le_of_partition a (fun k => k.val) b (fun k => (k.val : ℝ) ∈ S)
    hτ hδ hγ Λ n hb hinside houtside htotal

end Erdos522.LogMoments

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous limits of monotone distribution functions

Convergence on rational points determines a continuous limit everywhere.
Once pointwise convergence is known, compactness and monotonicity make the
convergence uniform on every compact subset of the real line.
-/

noncomputable section
open Filter Set Metric
open scoped Topology
namespace Erdos522

/-- Monotonicity and a continuous candidate limit extend rational-point convergence. -/
theorem tendsto_monotone_of_rational_convergence (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hmono : ∀ n, Monotone (f n)) (hg : Continuous g)
    (hq : ∀ q : ℚ, Tendsto (fun n => f n (q : ℝ)) atTop (𝓝 (g q))) (x : ℝ) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := x))
      (g x - a) (by linarith)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x - δ < x by linarith)
    have hd : dist (q : ℝ) x < δ := by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
    have hga : a < g q := by
      have hh := hnear hd
      rw [Real.dist_eq] at hh
      linarith [(abs_lt.mp hh).1]
    filter_upwards [(hq q).eventually_const_lt hga] with n hn
    exact hn.trans_le (hmono n hq₂.le)
  · intro a ha
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := x))
      (a - g x) (by linarith)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x < x + δ by linarith)
    have hd : dist (q : ℝ) x < δ := by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    have hga : g q < a := by
      have hh := hnear hd
      rw [Real.dist_eq] at hh
      linarith [(abs_lt.mp hh).2]
    filter_upwards [(hq q).eventually_lt_const hga] with n hn
    exact (hmono n hq₁.le).trans_lt hn

/-- Monotone real functions converging pointwise to a continuous limit converge
uniformly on every compact set. -/
theorem tendstoUniformlyOn_of_monotone_pointwise (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hmono : ∀ n, Monotone (f n)) (hg : Continuous g)
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {s : Set ℝ} (hs : IsCompact s) : TendstoUniformlyOn f g atTop s := by
  classical
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  choose δ hδ hnear using fun x : ℝ =>
    Metric.continuousAt_iff.mp (hg.continuousAt (x := x)) (ε / 3) he
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun x : ℝ => ball x (δ x / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, by simp only [mem_ball, dist_self]; exact div_pos (hδ x) (by norm_num)⟩)
  have hends : ∀ x : ℝ, ∀ᶠ n : ℕ in atTop,
      dist (f n (x - δ x / 2)) (g (x - δ x / 2)) < ε / 3 ∧
      dist (f n (x + δ x / 2)) (g (x + δ x / 2)) < ε / 3 := by
    intro x
    exact ((hpoint (x - δ x / 2)).eventually (ball_mem_nhds _ he)).and
      ((hpoint (x + δ x / 2)).eventually (ball_mem_nhds _ he))
  have hall : ∀ᶠ n : ℕ in atTop, ∀ x ∈ t,
      dist (f n (x - δ x / 2)) (g (x - δ x / 2)) < ε / 3 ∧
      dist (f n (x + δ x / 2)) (g (x + δ x / 2)) < ε / 3 :=
    (Filter.eventually_all_finset t).mpr (fun x _ => hends x)
  filter_upwards [hall] with n hn
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
  have hd : dist y x < δ x / 2 := hxy
  have hδx := hδ x
  have hly : x - δ x / 2 ≤ y := by
    rw [Real.dist_eq] at hd
    linarith [(abs_lt.mp hd).1]
  have hyu : y ≤ x + δ x / 2 := by
    rw [Real.dist_eq] at hd
    linarith [(abs_lt.mp hd).2]
  have hlow := hnear x (show dist (x - δ x / 2) x < δ x by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]
    linarith)
  have hupp := hnear x (show dist (x + δ x / 2) x < δ x by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith)
  have hmid := hnear x (show dist y x < δ x by linarith)
  have he₁ := (hn x hx).1
  have he₂ := (hn x hx).2
  rw [Real.dist_eq] at hlow hupp hmid he₁ he₂ ⊢
  apply abs_lt.mpr
  constructor <;>
    linarith [(abs_lt.mp hlow).1, (abs_lt.mp hlow).2,
      (abs_lt.mp hupp).1, (abs_lt.mp hupp).2, (abs_lt.mp hmid).1, (abs_lt.mp hmid).2,
      (abs_lt.mp he₁).1, (abs_lt.mp he₁).2, (abs_lt.mp he₂).1, (abs_lt.mp he₂).2,
      hmono n hly, hmono n hyu]

end Erdos522

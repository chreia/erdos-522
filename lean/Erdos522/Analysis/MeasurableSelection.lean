/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Bases

/-!
# Measurable selection from open sublevel sets

A countable dense family gives measurable approximate choices when the
objective is continuous in the choice variable and measurable in the parameter.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace Erdos522

/-- A nonempty open sublevel set admits a measurable choice from a countable dense family. -/
theorem exists_measurable_sublevel_selector
    {T X : Type*} [MeasurableSpace T] [TopologicalSpace X] [MeasurableSpace X]
    [SeparableSpace X] [Nonempty X]
    (F : T → X → ℝ) (b : T → ℝ)
    (hmeas : ∀ x, Measurable (fun t => F t x)) (hb : Measurable b)
    (hcont : ∀ t, Continuous (F t))
    (hexists : ∀ t, ∃ x, F t x < b t) :
    ∃ x : T → X, Measurable x ∧ ∀ t, F t (x t) < b t := by
  classical
  obtain ⟨u, hu⟩ := exists_dense_seq X
  have hchoice (t : T) : ∃ n : ℕ, F t (u n) < b t := by
    have hopen : IsOpen {x | F t x < b t} := isOpen_lt (hcont t) continuous_const
    obtain ⟨x, hx, n, rfl⟩ := (show Dense (Set.range u) from hu).inter_open_nonempty _ hopen (hexists t)
    exact ⟨n, hx⟩
  refine ⟨fun t => u (Nat.find (hchoice t)), ?_, ?_⟩
  · exact Measurable.find (fun _ => measurable_const)
      (fun n => measurableSet_lt (hmeas (u n)) hb) hchoice
  · intro t
    exact Nat.find_spec (hchoice t)

end Erdos522

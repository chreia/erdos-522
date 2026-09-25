/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
-- Modified in 2026 by Sebastien Kawada: ported to Lean v4.34.0 and Mathlib 5ed2965.
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {mu : Measure α}

/-- Convergence in L^1 yields an a.e.-convergent subsequence. -/
theorem exists_seq_tendsto_ae_of_tendsto_eLpNorm_one
    [NormedAddCommGroup E] {f : ℕ → α → E} {g : α → E}
    (_hf : ∀ n, AEStronglyMeasurable (f n) mu)
    (_hg : AEStronglyMeasurable g mu)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) (1 : ENNReal) mu) atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂mu, Tendsto (fun i => f (ns i) x) atTop (nhds (g x)) := by
  have h_in_measure : TendstoInMeasure mu f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ENNReal)) (by simp) hfg
  exact h_in_measure.exists_seq_tendsto_ae

end MeasureTheory

/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada

The definitions `KacCoefficients`, `KacCoefficients.polynomial`, `KacCoefficients.roots` and
`KacCoefficients.numRootsInUnitDisk`, their docstrings, and the statement and docstring of
`erdos_522` are copied from `FormalConjectures/ErdosProblems/522.lean` in
google-deepmind/formal-conjectures at commit 2424bb480c590237ffbb2cc831ae4cb8977e045a
(Copyright 2025 The Formal Conjectures Authors, Apache License 2.0).
-/

import Erdos522.Probability.IndependentCoefficientRadialLaws
import Mathlib.Probability.Distributions.Uniform

/-!
# The formal-conjectures statement of Erdős Problem #522

This file proves the statement `Erdos522.erdos_522` of google-deepmind/formal-conjectures
(file `FormalConjectures/ErdosProblems/522.lean`, commit `2424bb48`) from the Rademacher strong
law `Erdos522.erdos_522_of_independent_coins` of this project.

The definitions of formal-conjectures are reproduced verbatim in the namespace
`FormalConjectures.Erdos522Mirror`, and the statement text of `erdos_522` is reproduced verbatim,
with the following changes only, each forced by the absence of the formal-conjectures
infrastructure in this project:

* the namespace `Erdos522` is renamed `FormalConjectures.Erdos522Mirror`;
* the module header (`module`, `public import FormalConjecturesUtil`,
  `@[expose] public section`) is replaced by ordinary imports;
* the attribute `@[category research open, AMS 12 60]` is omitted;
* the open-problem placeholder inside `answer(·)` is replaced by `True`, with a local `answer(·)`
  notation that elaborates to its argument. Under the default `google.answer = always_true`
  option of formal-conjectures, the placeholder in a `Prop` position elaborates to `True`, so the
  proposition is unchanged.

Mathlib changed two relevant definitions between the revision pinned by formal-conjectures
(`0df444a`) and the revision used here (`5ed2965`). At `0df444a`, `pdf.IsUniform X s ℙ μ` is
`map X ℙ = ProbabilityTheory.cond μ s`, and `Measure.map` of a function that is not almost
everywhere measurable is `0`. At `5ed2965`, `pdf.IsUniform X s ℙ μ` is
`HasLaw X (ProbabilityTheory.cond μ s) ℙ`, which asks for almost-everywhere measurability together
with the same identity, and `Measure.map` of a function that is not almost everywhere measurable
is a Dirac mass (mathlib4#42322). Since `ProbabilityTheory.cond Measure.count {-1, 1}` is a
probability measure, at both revisions the field `h_unif i` says exactly that `c i` is almost
everywhere measurable with law `ProbabilityTheory.cond Measure.count {-1, 1}`. The proof uses
`h_unif` only through these two facts, which are the hypotheses of
`ae_tendsto_closedZeroCount_of_uniform`.

The file also checks that the hypotheses of `erdos_522` can be met: `rademacherKacCoefficients`
realises Kac coefficients over `{-1, 1}` on the space of infinite fair-coin sequences.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real

namespace FormalConjectures.Erdos522Mirror

/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S` with respect to the reference
measure `μ`. The default reference measure is the counting measure, so that for a finite set `S`
each coefficient takes every value of `S` with probability `1 / |S|`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count)

/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective P Q h := by aesop

namespace KacCoefficients

open scoped Polynomial

variable {S Ω} {μ : Measure k}

/--
The random polynomial associated to a sequence `c : KacCoefficients S Ω μ` of Kac coefficients
given by `∑ i ∈ Finset.range (n + 1), c i z^i`.
-/
noncomputable def polynomial (c : KacCoefficients S Ω μ) (n : ℕ) :
    Ω → k[X] := fun ω => ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i ω)

/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (c : KacCoefficients S Ω μ) (n : ℕ) : Ω → Multiset k :=
    fun ω => (c.polynomial n ω).roots

/-- Counts the number of roots of a Kac polynomial in the unit disk with multiplicity. -/
noncomputable def numRootsInUnitDisk [PseudoMetricSpace k] (c : KacCoefficients S Ω μ) (n : ℕ)
    (ω : Ω) : ℕ :=
  open scoped Classical in
  (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)

end KacCoefficients

end FormalConjectures.Erdos522Mirror

/-! ### The bridge to the Rademacher strong law -/

namespace FormalConjectures.Erdos522Mirror

open Erdos522 (closedZeroCount polynomialPrefix)

/-- The counting measure gives the coefficient set `{-1, 1}` mass two. -/
theorem count_neg_one_one : Measure.count ({-1, 1} : Set ℂ) = 2 := by
  rw [Measure.count_apply (Set.toFinite _).measurableSet, Set.encard_pair (by norm_num)]
  rfl

/-- The fair-coin label of a coefficient: `true` for `1` and `false` otherwise. -/
noncomputable def coinLabel (z : ℂ) : Bool := decide (z = 1)

/-- The fair-coin label is measurable. -/
theorem measurable_coinLabel : Measurable coinLabel :=
  measurable_to_countable' fun b => by
    cases b
    · have : coinLabel ⁻¹' {false} = {1}ᶜ := by ext z; simp [coinLabel]
      rw [this]
      exact (measurableSet_singleton 1).compl
    · have : coinLabel ⁻¹' {true} = {1} := by ext z; simp [coinLabel]
      rw [this]
      exact measurableSet_singleton 1

/-- Labelling the uniform law on `{-1, 1}` gives the fair-coin law on `Bool`. -/
theorem map_coinLabel_cond :
    (ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ)).map coinLabel =
      (PMF.uniformOfFintype Bool).toMeasure := by
  have hs : MeasurableSet ({-1, 1} : Set ℂ) := (Set.toFinite _).measurableSet
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.map_apply measurable_coinLabel (measurableSet_singleton b),
    ProbabilityTheory.cond_apply hs, count_neg_one_one,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  cases b
  · have : ({-1, 1} : Set ℂ) ∩ coinLabel ⁻¹' {false} = {-1} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage,
        coinLabel, decide_eq_false_iff_not]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd h h'
      · rintro rfl
        exact ⟨Or.inl rfl, by norm_num⟩
    rw [this, Measure.count_singleton]
    simp
  · have : ({-1, 1} : Set ℂ) ∩ coinLabel ⁻¹' {true} = {1} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage,
        coinLabel, decide_eq_true_eq]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨Or.inr rfl, rfl⟩
    rw [this, Measure.count_singleton]
    simp

/-- The Rademacher strong law for almost everywhere measurable, independent coefficients whose
laws are uniform on `{-1, 1}`. The two hypotheses on each coefficient are exactly the content of
`pdf.IsUniform (X i) {-1, 1} P Measure.count`, both at the Mathlib revision used here and at the
one pinned by formal-conjectures. -/
theorem ae_tendsto_closedZeroCount_of_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℂ} (hind : ProbabilityTheory.iIndepFun X P) (hX : ∀ i, AEMeasurable (X i) P)
    (hmap : ∀ i, P.map (X i) = ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ)) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (closedZeroCount (polynomialPrefix (fun k => X k ω) (fun _ => 1) N) 1 : ℝ) / N)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hs : MeasurableSet ({-1, 1} : Set ℂ) := (Set.toFinite _).measurableSet
  have hlaw : ∀ i, ProbabilityTheory.HasLaw (coinLabel ∘ X i)
      (PMF.uniformOfFintype Bool).toMeasure P := fun i =>
    ⟨measurable_coinLabel.comp_aemeasurable (hX i), by
      rw [← AEMeasurable.map_map_of_aemeasurable measurable_coinLabel.aemeasurable (hX i), hmap i,
        map_coinLabel_cond]⟩
  have hcoins := Erdos522.erdos_522_of_independent_coins hlaw
    (hind.comp (fun _ => coinLabel) (fun _ => measurable_coinLabel))
  have hmem : ∀ᵐ ω ∂P, ∀ k, X k ω ∈ ({-1, 1} : Set ℂ) := ae_all_iff.2 fun k =>
    ae_of_ae_map (hX k) (by rw [hmap k]; exact ProbabilityTheory.ae_cond_mem hs)
  filter_upwards [hcoins, hmem] with ω hω hmω
  have hsign : (fun k => Erdos522.LogMoments.sign ((coinLabel ∘ X k) ω)) = fun k => X k ω := by
    funext k
    rcases hmω k with h | h
    · have hne : (-1 : ℂ) ≠ 1 := by norm_num
      simp [coinLabel, Erdos522.LogMoments.sign, h, hne]
    · rw [Set.mem_singleton_iff] at h
      simp [coinLabel, Erdos522.LogMoments.sign, h]
  rwa [hsign] at hω

/-- The formal-conjectures root count is the closed-disk zero count of the polynomial prefix. -/
theorem numRootsInUnitDisk_eq_closedZeroCount {Ω : Type*} [MeasureSpace Ω] {S : Set ℂ}
    (c : KacCoefficients S Ω) (n : ℕ) (ω : Ω) :
    c.numRootsInUnitDisk n ω =
      closedZeroCount (polynomialPrefix (fun k => c.toFun k ω) (fun _ => 1) n) 1 := by
  classical
  have hpoly : c.polynomial n ω = polynomialPrefix (fun k => c.toFun k ω) (fun _ => 1) n := by
    simp only [KacCoefficients.polynomial, polynomialPrefix, mul_one,
      Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  simp only [KacCoefficients.numRootsInUnitDisk, KacCoefficients.roots, hpoly, closedZeroCount,
    Erdos522.zeroCountIn, Multiset.countP_eq_card_filter]
  congr 1
  exact Multiset.filter_congr fun z _ => by simp

/-- A local stand-in for the `answer(·)` syntax of formal-conjectures. -/
scoped syntax (name := answerMirror) "answer(" term ")" : term

macro_rules (kind := answerMirror)
  | `(answer($t)) => `($t)

/--
Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where
$\epsilon_k\in \{-1,1\}$ independently uniformly at random for $0\leq k\leq n$.

Is it true that, if $R_n$ is the number of roots of $f(z)$ in
$\{ z\in \mathbb{C} : \lvert z\rvert \leq 1\}$, then
$$
  \frac{R_n}{n/2}\to 1
$$
almost surely?

There is some ambiguity as to whether the intended coefficient set is $\{-1, 1\}$ or $\{0, 1\}$,
see `erdos_522.variants.zero_one` for the alternate version.
-/
theorem erdos_522 :
    answer(True) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : KacCoefficients ({-1, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1 := by
  refine iff_of_true trivial ?_
  intro Ω _ _ c
  have hae : ∀ᵐ ω ∂(ℙ : Measure Ω),
      atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1) := by
    filter_upwards [ae_tendsto_closedZeroCount_of_uniform c.h_indep
      (fun i => (c.h_unif i).aemeasurable) (fun i => (c.h_unif i).map_eq)] with ω hω
    have h2 := hω.const_mul 2
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h2
    refine h2.congr fun n => ?_
    rw [numRootsInUnitDisk_eq_closedZeroCount]
    ring
  exact (measure_congr (ae_eq_univ.2 (mem_ae_iff.1 hae))).trans measure_univ

/-! ### The hypotheses of `erdos_522` are satisfiable -/

/-- The sample space of one infinite sequence of fair coins. -/
def CoinSequence : Type := ℕ → Bool

/-- The coin sequence space carries the infinite product of fair-coin laws. -/
noncomputable instance : MeasureSpace CoinSequence where
  toMeasurableSpace := MeasurableSpace.pi
  volume := Erdos522.rademacherSequenceMeasure

instance : IsProbabilityMeasure (ℙ : Measure CoinSequence) :=
  inferInstanceAs (IsProbabilityMeasure Erdos522.rademacherSequenceMeasure)

/-- The sign of a fair coin is measurable. -/
theorem measurable_sign : Measurable Erdos522.LogMoments.sign :=
  measurable_of_countable _

/-- The sign of a fair coin is uniform on `{-1, 1}` for the counting measure. -/
theorem map_sign_uniformOfFintype :
    (PMF.uniformOfFintype Bool).toMeasure.map Erdos522.LogMoments.sign =
      ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ) := by
  have hs : MeasurableSet ({-1, 1} : Set ℂ) := (Set.toFinite _).measurableSet
  have hid : (ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ)).map
      (Erdos522.LogMoments.sign ∘ coinLabel) =
        (ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ)).map id := by
    refine Measure.map_congr ?_
    filter_upwards [ProbabilityTheory.ae_cond_mem hs] with z hz
    rcases hz with rfl | hz
    · have hne : (-1 : ℂ) ≠ 1 := by norm_num
      simp [coinLabel, Erdos522.LogMoments.sign, hne]
    · rw [Set.mem_singleton_iff] at hz
      simp [coinLabel, Erdos522.LogMoments.sign, hz]
  rw [← map_coinLabel_cond, Measure.map_map measurable_sign measurable_coinLabel, hid,
    Measure.map_id]

/-- Independent fair signs on the coin sequence space are Kac coefficients over `{-1, 1}`, so the
universally quantified statement `erdos_522` is not vacuous. -/
noncomputable def rademacherKacCoefficients :
    KacCoefficients ({-1, 1} : Set ℂ) CoinSequence where
  toFun k ω := Erdos522.LogMoments.sign (ω k)
  h_indep := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
    (X := fun _ => Erdos522.LogMoments.sign) (fun _ => measurable_sign)
  h_unif i := by
    have hmeas : Measurable (fun ω : ℕ → Bool => Erdos522.LogMoments.sign (ω i)) :=
      measurable_sign.comp (measurable_pi_apply i)
    refine ProbabilityTheory.HasLaw.mk hmeas.aemeasurable ?_
    change Measure.map (Erdos522.LogMoments.sign ∘ fun ω : ℕ → Bool => ω i)
      (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) = _
    rw [← Measure.map_map measurable_sign (measurable_pi_apply i), Measure.infinitePi_map_eval,
      map_sign_uniformOfFintype]

end FormalConjectures.Erdos522Mirror

#print axioms FormalConjectures.Erdos522Mirror.erdos_522
#print axioms FormalConjectures.Erdos522Mirror.ae_tendsto_closedZeroCount_of_uniform
#print axioms FormalConjectures.Erdos522Mirror.numRootsInUnitDisk_eq_closedZeroCount
#print axioms FormalConjectures.Erdos522Mirror.rademacherKacCoefficients

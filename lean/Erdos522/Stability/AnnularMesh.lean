/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Stability.MeshDetection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Round

/-!
# A finite mesh of a thin annulus

Equally spaced radial rows include both endpoints of the annulus. Angular rows
have step at most a quarter of the prescribed distance scale. Their cardinality
is controlled explicitly in terms of the derivative-mesh parameters.
-/

noncomputable section

namespace Erdos522

/-- The number of radial subintervals in the annular mesh. -/
def annularRadialIntervals (N : ℕ) (K h : ℝ) : ℕ := ⌈2 * K / ((N : ℝ) * h)⌉₊

/-- The number of equally spaced angular samples. -/
def annularAngularSamples (h : ℝ) : ℕ := ⌈8 * Real.pi / h⌉₊

/-- The radial-angular mesh index set, including both radial endpoints. -/
abbrev AnnularMeshIndex (N : ℕ) (K h : ℝ) :=
  Fin (annularRadialIntervals N K h + 1) × Fin (annularAngularSamples h)

/-- The radial coordinate of a mesh row. -/
def annularMeshRadius (N : ℕ) (K h : ℝ)
    (i : Fin (annularRadialIntervals N K h + 1)) : ℝ :=
  1 - K / N + (2 * K / N) * (i.val : ℝ) / annularRadialIntervals N K h

/-- The angle in radians of a mesh column. -/
def annularMeshAngle (h : ℝ) (i : Fin (annularAngularSamples h)) : Real.Angle :=
  ((2 * Real.pi * i.val / annularAngularSamples h : ℝ) : Real.Angle)

/-- A point of the annular mesh. -/
def annularMeshPoint (N : ℕ) (K h : ℝ) (i : AnnularMeshIndex N K h) : ℂ :=
  (annularMeshRadius N K h i.1 : ℂ) * ((annularMeshAngle h i.2).toCircle : ℂ)

/-- The radial mesh has at most `(2K+2)/(Nh)` rows when `Nh≤1`. -/
theorem annular_radial_rows_le {N : ℕ} (hN : 0 < N) {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (hNh : (N : ℝ) * h ≤ 1) :
    (annularRadialIntervals N K h + 1 : ℝ) ≤ (2 * K + 2) / ((N : ℝ) * h) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * K / ((N : ℝ) * h))).le
  change (⌈2 * K / ((N : ℝ) * h)⌉₊ : ℝ) + 1 ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have hc' : (⌈2 * K / ((N : ℝ) * h)⌉₊ : ℝ) * ((N : ℝ) * h) ≤
      2 * K + (N : ℝ) * h := by
    have hmul := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (N : ℝ) * h)
    have heq : (2 * K / ((N : ℝ) * h) + 1) * ((N : ℝ) * h) =
        2 * K + (N : ℝ) * h := by field_simp
    rwa [heq] at hmul
  nlinarith

/-- At scale at most one, the angular mesh has at most `32/h` samples. -/
theorem annular_angular_samples_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (annularAngularSamples h : ℝ) ≤ 32 / h := by
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * Real.pi / h)).le
  apply (le_div_iff₀ hh).mpr
  have hmul := mul_le_mul_of_nonneg_right hc hh.le
  have heq : (8 * Real.pi / h + 1) * h = 8 * Real.pi + h := by field_simp
  rw [heq] at hmul
  change (⌈8 * Real.pi / h⌉₊ : ℝ) * h ≤ 32
  linarith [Real.pi_lt_d2]

/-- The explicit cardinality bound for a radial-angular annular mesh. -/
theorem annular_mesh_cardinality_le {N : ℕ} (hN : 2 ≤ N) {K S L : ℝ}
    (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) :
    (Fintype.card (AnnularMeshIndex N K (derivativeMeshSpacing N S L)) : ℝ) ≤
      2 ^ 18 * (K + 1) * S ^ 2 * N * L ^ 2 * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hS0 : 0 < S := by linarith
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hsqrt : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog
  have hh := derivativeMeshSpacing_le_inv_degree hN hS hL
  have hNh : (N : ℝ) * derivativeMeshSpacing N S L ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hh.2 hN0.le
    simpa only [mul_one_div, div_self hN0.ne'] using hm
  have hh1 : derivativeMeshSpacing N S L ≤ 1 := hh.2.trans
    ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hN1).trans_eq (by norm_num))
  have hrad := annular_radial_rows_le (by omega : 0 < N) hK hh.1 hNh
  have hang := annular_angular_samples_le hh.1 hh1
  simp only [AnnularMeshIndex, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  calc
    _ ≤ ((2 * K + 2) / ((N : ℝ) * derivativeMeshSpacing N S L)) *
        (32 / derivativeMeshSpacing N S L) := mul_le_mul hrad hang (Nat.cast_nonneg _) (div_nonneg (by linarith) (mul_nonneg hN0.le hh.1.le))
    _ = _ := by
      unfold derivativeMeshSpacing
      field_simp
      rw [Real.sq_sqrt hlog.le]
      ring

/-- Every point of `[0,q]` is within one half of an integer in the same interval. -/
theorem exists_nearest_finite_integer (q : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxq : x ≤ q) :
    ∃ i : Fin (q + 1), |x - (i.val : ℝ)| ≤ 1 / 2 := by
  have hround := abs_sub_round x
  have hrl : (0 : ℤ) ≤ round x := by
    have hr : (-1 : ℝ) < (round x : ℝ) := by
      have := (abs_le.mp hround).2
      linarith
    have hr' : (-1 : ℤ) < round x := by exact_mod_cast hr
    omega
  have hru : round x ≤ (q : ℤ) := by
    have hr : (round x : ℝ) < (q : ℝ) + 1 := by
      have := (abs_le.mp hround).1
      linarith
    have hr' : round x < (q : ℤ) + 1 := by exact_mod_cast hr
    omega
  have hcast : ((round x).toNat : ℝ) = (round x : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hrl
  have hi : (round x).toNat < q + 1 := by omega
  refine ⟨⟨(round x).toNat, hi⟩, ?_⟩
  simpa only [hcast] using hround

/-- The equally spaced radial rows form an `h/2`-net of the radial interval. -/
theorem exists_near_annularMeshRadius {N : ℕ} (hN : 0 < N) {K h r : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (hr : |r - 1| ≤ K / N) :
    ∃ i : Fin (annularRadialIntervals N K h + 1),
      |r - annularMeshRadius N K h i| ≤ h / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hK0 : K = 0
  · have hr1 : r = 1 := by
      have hz : r - 1 = 0 := by simpa [hK0] using hr
      linarith
    subst r
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [annularMeshRadius, hK0, zero_div, sub_zero, mul_zero, zero_mul, add_zero, sub_self, abs_zero]
    positivity
  have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
  let q := annularRadialIntervals N K h
  have hq : 0 < q := Nat.ceil_pos.mpr (by positivity)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  let W := 2 * K / (N : ℝ)
  have hW : 0 < W := by dsimp [W]; positivity
  let x := (q : ℝ) * (r - (1 - K / N)) / W
  have hx0 : 0 ≤ x := by
    have hlo : 0 ≤ r - (1 - K / N) := by linarith [(abs_le.mp hr).1]
    dsimp [x]
    positivity
  have hxq : x ≤ q := by
    apply (div_le_iff₀ hW).mpr
    apply mul_le_mul_of_nonneg_left _ hq0.le
    dsimp [W]
    have htwo : 2 * K / (N : ℝ) = 2 * (K / N) := by ring
    rw [htwo]
    linarith [(abs_le.mp hr).2]
  obtain ⟨i, hi⟩ := exists_nearest_finite_integer q hx0 hxq
  refine ⟨i, ?_⟩
  have hidentity : r - annularMeshRadius N K h i = (W / q) * (x - i.val) := by
    change r - (1 - K / N + W * i.val / q) = (W / q) *
      ((q : ℝ) * (r - (1 - K / N)) / W - i.val)
    field_simp
    ring
  rw [hidentity, abs_mul, abs_of_pos (div_pos hW hq0)]
  have hstep : W / q ≤ h := by
    have hc : 2 * K / ((N : ℝ) * h) ≤ (q : ℝ) := Nat.le_ceil _
    have hc' := (div_le_iff₀ (by positivity : 0 < (N : ℝ) * h)).mp hc
    apply (div_le_iff₀ hq0).mpr
    dsimp [W]
    apply (div_le_iff₀ hN0).mpr
    nlinarith
  calc
    (W / q) * |x - i.val| ≤ (W / q) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hi (div_nonneg hW.le hq0.le)
    _ ≤ h / 2 := by linarith

/-- The radial rows lie between the two prescribed annular endpoints. -/
theorem annularMeshRadius_mem {N : ℕ} (hN : 0 < N) {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (i : Fin (annularRadialIntervals N K h + 1)) :
    1 - K / N ≤ annularMeshRadius N K h i ∧ annularMeshRadius N K h i ≤ 1 + K / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hK0 : K = 0
  · simp [annularMeshRadius, hK0]
  have hKp : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
  have hq : 0 < annularRadialIntervals N K h := Nat.ceil_pos.mpr (by positivity)
  have hq0 : (0 : ℝ) < annularRadialIntervals N K h := by exact_mod_cast hq
  have hi : (i.val : ℝ) ≤ annularRadialIntervals N K h := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hratio : (i.val : ℝ) / annularRadialIntervals N K h ≤ 1 :=
    (div_le_one₀ hq0).mpr hi
  have hfrac : 0 ≤ 2 * K / (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hratio hfrac
  have hnonneg : 0 ≤ (2 * K / (N : ℝ)) * i.val / annularRadialIntervals N K h := by positivity
  unfold annularMeshRadius
  rw [mul_div_assoc] at hnonneg ⊢
  have htwo : 2 * K / (N : ℝ) = 2 * (K / N) := by ring
  rw [htwo] at hmul hnonneg ⊢
  constructor <;> nlinarith

/-- The exponential parametrization of the circle does not increase real angular distances. -/
theorem norm_circle_exp_sub_le (x y : ℝ) :
    ‖(Circle.exp x : ℂ) - (Circle.exp y : ℂ)‖ ≤ |x - y| := by
  have heq : Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y) =
      (Complex.exp (Complex.I * (x - y : ℝ)) - 1) * Complex.exp (Complex.I * y) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [Circle.coe_exp]
  rw [show (x : ℂ) * Complex.I = Complex.I * x by ring,
    show (y : ℂ) * Complex.I = Complex.I * y by ring,
    heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Angular mesh columns give simultaneous angular and chord approximation within `h/4`. -/
theorem exists_near_annularMeshAngle {h : ℝ} (hh : 0 < h) (θ : Real.Angle) :
    ∃ i : Fin (annularAngularSamples h), dist θ (annularMeshAngle h i) ≤ h / 4 ∧
      ‖(θ.toCircle : ℂ) - ((annularMeshAngle h i).toCircle : ℂ)‖ ≤ h / 4 := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let x : ℝ := AddCircle.equivIco (2 * Real.pi) 0 θ
  have hx0 : 0 ≤ x := (AddCircle.equivIco (2 * Real.pi) 0 θ).property.1
  have hx2pi : x < 2 * Real.pi := by simpa using (AddCircle.equivIco (2 * Real.pi) 0 θ).property.2
  have hxθ : (x : Real.Angle) = θ := AddCircle.coe_equivIco
  let J := annularAngularSamples h
  have hJ : 0 < J := Nat.ceil_pos.mpr (by positivity)
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  let u := (J : ℝ) * x / (2 * Real.pi)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have huJ : u < J := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    nlinarith
  have hi : ⌊u⌋₊ < J := (Nat.floor_lt hu0).mpr huJ
  let i : Fin J := ⟨⌊u⌋₊, hi⟩
  let y := 2 * Real.pi * i.val / (J : ℝ)
  have hdiff : |x - y| ≤ 2 * Real.pi / J := by
    have heq : x - y = (2 * Real.pi / J) * (u - (i.val : ℝ)) := by
      dsimp [y, u]
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / (J : ℝ))]
    have hf : |u - (i.val : ℝ)| ≤ 1 := Nat.abs_sub_floor_le hu0
    nlinarith [mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * Real.pi / (J : ℝ))]
  have hstep : 2 * Real.pi / (J : ℝ) ≤ h / 4 := by
    have hc : 8 * Real.pi / h ≤ (J : ℝ) := Nat.le_ceil _
    have hc' := (div_le_iff₀ hh).mp hc
    apply (div_le_iff₀ hJ0).mpr
    nlinarith
  have hdiffh := hdiff.trans hstep
  refine ⟨i, ?_, ?_⟩
  · rw [← hxθ]
    change dist (x : Real.Angle) (y : Real.Angle) ≤ h / 4
    rw [dist_eq_norm, ← Real.Angle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm.trans (by simpa only [Real.norm_eq_abs] using hdiffh)
  · rw [← hxθ]
    change ‖(Circle.exp x : ℂ) - (Circle.exp y : ℂ)‖ ≤ h / 4
    exact (norm_circle_exp_sub_le x y).trans hdiffh

/-- Every mesh point belongs to the original annulus. -/
theorem annularMeshPoint_mem {N : ℕ} (hN : 0 < N) {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (hKN : K ≤ (N : ℝ)) (i : AnnularMeshIndex N K h) :
    |‖annularMeshPoint N K h i‖ - 1| ≤ K / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr := annularMeshRadius_mem hN hK hh i.1
  have hfrac := (div_le_one₀ hN0).mpr hKN
  have hr0 : 0 ≤ annularMeshRadius N K h i.1 := by linarith
  simp only [annularMeshPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Circle.norm_coe, mul_one, abs_of_nonneg hr0]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The explicit radial-angular grid covers every point of the annulus and tracks its angle. -/
theorem exists_near_annularMeshPoint {N : ℕ} (hN : 0 < N) {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (hKN : K ≤ (N : ℝ)) {α : ℂ}
    (hα : |‖α‖ - 1| ≤ K / N) :
    ∃ i : AnnularMeshIndex N K h, ‖α - annularMeshPoint N K h i‖ ≤ h ∧
      dist (Complex.arg α : Real.Angle) (annularMeshAngle h i.2) ≤ h / 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨i, hi⟩ := exists_near_annularMeshRadius hN hK hh hα
  obtain ⟨j, hj, hchord⟩ := exists_near_annularMeshAngle hh (Complex.arg α : Real.Angle)
  let θ : Real.Angle := Complex.arg α
  let s := annularMeshRadius N K h i
  have hpolar : α = (‖α‖ : ℂ) * (θ.toCircle : ℂ) := by
    simpa only [θ, Real.Angle.toCircle_coe, Circle.coe_exp] using
      (Complex.norm_mul_exp_arg_mul_I α).symm
  have hs := annularMeshRadius_mem hN hK hh i
  have hfrac := (div_le_one₀ hN0).mpr hKN
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs2 : s ≤ 2 := by dsimp [s]; linarith
  refine ⟨(i, j), ?_, hj⟩
  have heq : α - annularMeshPoint N K h (i, j) =
      ((‖α‖ - s : ℝ) : ℂ) * (θ.toCircle : ℂ) +
      (s : ℂ) * ((θ.toCircle : ℂ) - ((annularMeshAngle h j).toCircle : ℂ)) := by
    nth_rw 1 [hpolar]
    dsimp [annularMeshPoint, s]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖((‖α‖ - s : ℝ) : ℂ) * (θ.toCircle : ℂ)‖ +
        ‖(s : ℂ) * ((θ.toCircle : ℂ) - ((annularMeshAngle h j).toCircle : ℂ))‖ := norm_add_le _ _
    _ = |‖α‖ - s| + s * ‖(θ.toCircle : ℂ) - ((annularMeshAngle h j).toCircle : ℂ)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
        mul_one, abs_of_nonneg hs0]
    _ ≤ h / 2 + 2 * (h / 4) := add_le_add hi
      (mul_le_mul hs2 hchord (norm_nonneg _) (by norm_num))
    _ = h := by ring

/-- Mesh cells fit into a unit-circle-centered disk at scale `(K+1)/N`. -/
theorem annular_mesh_cell_containment {N : ℕ} (hN : 0 < N) {K h : ℝ}
    (hK : 0 ≤ K) (hh : 0 < h) (_hKN : K ≤ (N : ℝ)) (hhN : h ≤ 1 / (N : ℝ))
    (i : AnnularMeshIndex N K h) :
    Metric.closedBall (annularMeshPoint N K h i) h ⊆
      Metric.closedBall ((annularMeshAngle h i.2).toCircle : ℂ) ((K + 1) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr := annularMeshRadius_mem hN hK hh i.1
  have hcenter : ‖annularMeshPoint N K h i - ((annularMeshAngle h i.2).toCircle : ℂ)‖ ≤ K / N := by
    unfold annularMeshPoint
    rw [show (annularMeshRadius N K h i.1 : ℂ) * ((annularMeshAngle h i.2).toCircle : ℂ) -
        ((annularMeshAngle h i.2).toCircle : ℂ) =
      ((annularMeshRadius N K h i.1 - 1 : ℝ) : ℂ) * ((annularMeshAngle h i.2).toCircle : ℂ) by
        push_cast; ring]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  intro z hz
  change dist z _ ≤ _
  have hzd : dist z (annularMeshPoint N K h i) ≤ h := hz
  have hc : dist (annularMeshPoint N K h i) ((annularMeshAngle h i.2).toCircle : ℂ) ≤ K / N := by
    simpa only [dist_eq_norm] using hcenter
  have htri := dist_triangle z (annularMeshPoint N K h i) ((annularMeshAngle h i.2).toCircle : ℂ)
  have heq : (K + 1) / (N : ℝ) = K / N + 1 / N := by ring
  rw [heq]
  linarith

/-- Every annular small-derivative root outside the doubled sectors is detected at a retained mesh point. -/
theorem exists_retained_annular_root_mesh_detection (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K S L : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L) (hKN : K + 1 ≤ (N : ℝ))
    {α : ℂ} (hα : |‖α‖ - 1| ≤ K / N) (hroot : P.eval α = 0)
    (hderiv : ‖P.derivative.eval α‖ ≤ (N : ℝ) ^ (3 / 2 : ℝ) / L)
    (hangle : 2 / Real.sqrt N ≤ realAxisAngularDistance (Complex.arg α : Real.Angle))
    (hbound : ∀ w, ‖w‖ ≤ 1 + (K + 1) / N →
      ‖P.derivative.derivative.eval w‖ ≤ S * (N : ℝ) ^ (5 / 2 : ℝ) * Real.sqrt (Real.log N)) :
    ∃ i : AnnularMeshIndex N K (derivativeMeshSpacing N S L),
      ‖α - annularMeshPoint N K (derivativeMeshSpacing N S L) i‖ ≤ derivativeMeshSpacing N S L ∧
      1 / Real.sqrt N ≤ realAxisAngularDistance (annularMeshAngle (derivativeMeshSpacing N S L) i.2) ∧
      ‖P.eval (annularMeshPoint N K (derivativeMeshSpacing N S L) i)‖ / Real.sqrt N ≤
        derivativeMeshValueThreshold N S L ∧
      ‖annularMeshPoint N K (derivativeMeshSpacing N S L) i *
        P.derivative.eval (annularMeshPoint N K (derivativeMeshSpacing N S L) i)‖ /
          (N : ℝ) ^ (3 / 2 : ℝ) ≤ 3 / L := by
  have hh := derivativeMeshSpacing_le_inv_degree hN hS hL
  obtain ⟨i, hi, hia⟩ := exists_near_annularMeshPoint (by omega : 0 < N) hK hh.1
    (by linarith : K ≤ (N : ℝ)) hα
  have hdist : dist (Complex.arg α : Real.Angle)
      (annularMeshAngle (derivativeMeshSpacing N S L) i.2) ≤ derivativeMeshSpacing N S L := by
    linarith [hh.1]
  have hnear : ‖annularMeshPoint N K (derivativeMeshSpacing N S L) i - α‖ ≤
      derivativeMeshSpacing N S L := by simpa only [norm_sub_rev] using hi
  exact ⟨i, hi, derivative_mesh_sector_retention hN hS hL hangle hdist,
    annular_root_mesh_detection_rpow P hN hK hS hL hKN hα hroot hderiv hnear hbound⟩

/-- A local count around every unit-circle point bounds each mesh cell, with multiplicity. -/
theorem annular_mesh_cell_zero_count_le (P : Polynomial ℂ) {N : ℕ} (hN : 2 ≤ N)
    {K K' S L B : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hKN : K ≤ (N : ℝ)) (hK' : K + 1 ≤ 2 * K')
    (hlocal : ∀ c : ℂ, ‖c‖ = 1 →
      (zeroCountIn P (Metric.closedBall c (2 * K' / N)) : ℝ) ≤ B)
    (i : AnnularMeshIndex N K (derivativeMeshSpacing N S L)) :
    (zeroCountIn P (Metric.closedBall (annularMeshPoint N K (derivativeMeshSpacing N S L) i)
      (derivativeMeshSpacing N S L)) : ℝ) ≤ B := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hh := derivativeMeshSpacing_le_inv_degree hN hS hL
  have hcontain := annular_mesh_cell_containment (by omega : 0 < N) hK hh.1 hKN hh.2 i
  have hrad : (K + 1) / (N : ℝ) ≤ 2 * K' / N := div_le_div_of_nonneg_right hK' hN0.le
  have hsub := hcontain.trans (Metric.closedBall_subset_closedBall hrad)
  have hcount : (zeroCountIn P (Metric.closedBall
      (annularMeshPoint N K (derivativeMeshSpacing N S L) i) (derivativeMeshSpacing N S L)) : ℝ) ≤
      zeroCountIn P (Metric.closedBall
        ((annularMeshAngle (derivativeMeshSpacing N S L) i.2).toCircle : ℂ) (2 * K' / N)) := by
    exact_mod_cast zeroCountIn_mono P hsub
  exact hcount.trans (hlocal _ (Circle.norm_coe _))

end Erdos522

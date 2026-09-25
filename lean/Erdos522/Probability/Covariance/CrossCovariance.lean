/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.JetCovariance

/-!
# Covariance of separated polynomial jets

Products of real projections contain both an ordinary and a conjugate
Fourier phase. Bounds at both angular separations control the cross form
and preserve nondegeneracy of the pair of four-dimensional jets.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Erdos522

/-- The mixed radial-index kernel for two possibly different radii. -/
def crossRadialIndexKernel (N j : ℕ) (r s : ℝ) (z : ℂ) : ℂ :=
  (1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
    (((r * s) ^ k * ((k : ℝ) / N) ^ j : ℝ) : ℂ) * z ^ k

/-- Expanding a product of affine coefficients uses three mixed kernels. -/
theorem affine_product_kernel (N : ℕ) (r s : ℝ) (z u v p q : ℂ) :
    (1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
      ((r * s) ^ k : ℝ) * (u + ((k : ℝ) / N : ℝ) * v) *
        (p + ((k : ℝ) / N : ℝ) * q) * z ^ k =
      (u * p) * crossRadialIndexKernel N 0 r s z +
        (u * q + v * p) * crossRadialIndexKernel N 1 r s z +
        (v * q) * crossRadialIndexKernel N 2 r s z := by
  unfold crossRadialIndexKernel
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- The bilinear combination of three radial-index kernels. -/
def affineProductKernel (N : ℕ) (r s : ℝ) (z u v p q : ℂ) : ℂ :=
  (u * p) * crossRadialIndexKernel N 0 r s z +
    (u * q + v * p) * crossRadialIndexKernel N 1 r s z +
    (v * q) * crossRadialIndexKernel N 2 r s z

/-- Three mixed kernel bounds control the bilinear form in arbitrary directions. -/
theorem norm_affineProductKernel_le (N : ℕ) (r s : ℝ) (z u v p q : ℂ)
    (ε : ℝ)
    (hkernel : ∀ j ≤ 2, ‖crossRadialIndexKernel N j r s z‖ ≤ ε) :
    ‖affineProductKernel N r s z u v p q‖ ≤
      ε * (‖u‖ + ‖v‖) * (‖p‖ + ‖q‖) := by
  unfold affineProductKernel
  calc
    _ ≤ ‖(u * p) * crossRadialIndexKernel N 0 r s z‖ +
        ‖(u * q + v * p) * crossRadialIndexKernel N 1 r s z‖ +
        ‖(v * q) * crossRadialIndexKernel N 2 r s z‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (‖u‖ * ‖p‖) * ε + (‖u‖ * ‖q‖ + ‖v‖ * ‖p‖) * ε +
        (‖v‖ * ‖q‖) * ε := by
      simp only [norm_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hkernel 0 (by omega)) (by positivity)
        · apply mul_le_mul _ (hkernel 1 (by omega)) (norm_nonneg _) (by positivity)
          simpa only [norm_mul] using norm_add_le (u * q) (v * p)
      · exact mul_le_mul_of_nonneg_left (hkernel 2 le_rfl) (by positivity)
    _ = _ := by ring

/-- Multiplying real projections produces ordinary and conjugate phases. -/
theorem real_projection_product (a b : ℂ) :
    2 * a.re * b.re = (a * conj b).re + (a * b).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The normalized cross covariance of two polynomial jets. -/
def crossJetCovarianceForm (N : ℕ) (r s : ℝ) (z w u v p q : ℂ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1), (r * s) ^ k *
    (((u + ((k : ℝ) / N : ℝ) * v) * z ^ k).re) *
    (((p + ((k : ℝ) / N : ℝ) * q) * w ^ k).re)

/-- The two Fourier phases in the product of affine jet projections. -/
theorem real_projection_product_phases (t : ℝ) (k : ℕ) (z w u v p q : ℂ) :
    2 * (((u + t * v) * z ^ k).re) * (((p + t * q) * w ^ k).re) =
      ((u + t * v) * (conj p + t * conj q) * (z * conj w) ^ k).re +
      ((u + t * v) * (p + t * q) * (z * w) ^ k).re := by
  rw [real_projection_product]
  congr 1
  · congr 1
    simp only [map_mul, map_add, map_pow, Complex.conj_ofReal, mul_pow]
    ring
  · congr 1
    rw [mul_pow]
    ring

/-- The cross covariance splits into the kernels at the angular difference and sum. -/
theorem crossJetCovarianceForm_decomposition (N : ℕ) (r s : ℝ) (z w u v p q : ℂ) :
    2 * crossJetCovarianceForm N r s z w u v p q =
      (affineProductKernel N r s (z * conj w) u v (conj p) (conj q)).re +
      (affineProductKernel N r s (z * w) u v p q).re := by
  unfold affineProductKernel
  rw [← affine_product_kernel, ← affine_product_kernel]
  have real_mul_re (a : ℝ) (b : ℂ) : ((a : ℂ) * b).re = a * b.re := by simp
  have hscale (a : ℂ) : ((1 / (N : ℂ)) * a).re = (1 / (N : ℝ)) * a.re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
    exact real_mul_re _ _
  rw [hscale, hscale, Complex.re_sum, Complex.re_sum, ← mul_add,
    ← Finset.sum_add_distrib]
  unfold crossJetCovarianceForm
  rw [mul_left_comm (2 : ℝ), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc (((r * s) ^ k : ℝ) : ℂ), real_mul_re]
  have h := real_projection_product_phases ((k : ℝ) / N) k z w u v p q
  nlinarith [congrArg (fun t : ℝ => (r * s) ^ k * t) h]

/-- Both Fourier kernels are needed to control the dependence of two real jets. -/
theorem abs_crossJetCovarianceForm_le (N : ℕ) (r s : ℝ) (z w u v p q : ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hminus : ∀ j ≤ 2, ‖crossRadialIndexKernel N j r s (z * conj w)‖ ≤ ε)
    (hplus : ∀ j ≤ 2, ‖crossRadialIndexKernel N j r s (z * w)‖ ≤ ε) :
    |crossJetCovarianceForm N r s z w u v p q| ≤
      ε * (‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2)) := by
  have hm := norm_affineProductKernel_le N r s (z * conj w) u v (conj p) (conj q) ε hminus
  have hp := norm_affineProductKernel_le N r s (z * w) u v p q ε hplus
  simp only [Complex.norm_conj] at hm
  have habs : |2 * crossJetCovarianceForm N r s z w u v p q| ≤
      2 * (ε * (‖u‖ + ‖v‖) * (‖p‖ + ‖q‖)) := by
    rw [crossJetCovarianceForm_decomposition]
    exact (abs_add_le _ _).trans (by
      have hm' := (Complex.abs_re_le_norm _).trans hm
      have hp' := (Complex.abs_re_le_norm _).trans hp
      linarith)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  have hprod : (‖u‖ + ‖v‖) * (‖p‖ + ‖q‖) ≤
      ‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖p‖ - ‖q‖),
      sq_nonneg (‖u‖ + ‖v‖ - (‖p‖ + ‖q‖))]
  have hmul := mul_le_mul_of_nonneg_left hprod hε
  nlinarith

/-- The eight-dimensional covariance form of a pair of normalized jets. -/
def pairedJetCovarianceForm (N : ℕ) (r s : ℝ) (z w u v p q : ℂ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
    (r ^ k * (((u + ((k : ℝ) / N : ℝ) * v) * z ^ k).re) +
      s ^ k * (((p + ((k : ℝ) / N : ℝ) * q) * w ^ k).re)) ^ 2

/-- The paired covariance consists of its two diagonal forms and twice the cross form. -/
theorem pairedJetCovarianceForm_decomposition (N : ℕ) (r s : ℝ) (z w u v p q : ℂ) :
    pairedJetCovarianceForm N r s z w u v p q =
      jetCovarianceForm N r z u v + jetCovarianceForm N s w p q +
        2 * crossJetCovarianceForm N r s z w u v p q := by
  have hpoint (k : ℕ) (a b : ℝ) : (r ^ k * a + s ^ k * b) ^ 2 =
      r ^ (2 * k) * a ^ 2 + s ^ (2 * k) * b ^ 2 + 2 * ((r * s) ^ k * a * b) := by
    simp only [show 2 * k = k * 2 by omega, pow_mul, mul_pow]
    ring
  unfold pairedJetCovarianceForm jetCovarianceForm crossJetCovarianceForm
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- A cross covariance of size at most a quarter of the marginal lower bound
preserves half that lower bound for the paired form. -/
theorem pairedJetCovarianceForm_lower (N : ℕ) (r s : ℝ) (z w u v p q : ℂ)
    (c : ℝ)
    (hr : c * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ jetCovarianceForm N r z u v)
    (hs : c * (‖p‖ ^ 2 + ‖q‖ ^ 2) ≤ jetCovarianceForm N s w p q)
    (hcross : |crossJetCovarianceForm N r s z w u v p q| ≤
      c / 4 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2))) :
    c / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2)) ≤
      pairedJetCovarianceForm N r s z w u v p q := by
  rw [pairedJetCovarianceForm_decomposition]
  have h := (abs_le.mp hcross).1
  nlinarith

/-- The mixed kernel has the same Abel constant for possibly unequal radii. -/
theorem crossRadialIndexKernel_bound (N j : ℕ) (hN : 0 < N) (K r s t : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N) (ht : (t : Real.Angle) ≠ 0) :
    ‖crossRadialIndexKernel N j r s (Complex.exp (Complex.I * t))‖ ≤
      10 * Real.exp (4 * K) / ((N : ℝ) * ‖(t : Real.Angle)‖) :=
  normalized_radial_index_sum_le_angle_norm N j hN K r s t hK hr0 hs0 hr hs ht

/-- A square-degree threshold and inverse-square-root separation give a product bound. -/
theorem degree_times_separation_lower (N : ℕ) (hN : 0 < N) (A δ : ℝ)
    (hA : 0 ≤ A) (hdegree : A ^ 2 ≤ (N : ℝ)) (hδ : 1 / Real.sqrt N ≤ δ) :
    A ≤ (N : ℝ) * δ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  have hbound : A ≤ Real.sqrt N := by nlinarith
  calc
    A ≤ Real.sqrt N := hbound
    _ = (N : ℝ) * (1 / Real.sqrt N) := by
      rw [mul_one_div]
      apply (eq_div_iff hs.ne').mpr
      simpa only [pow_two] using hsq
    _ ≤ _ := mul_le_mul_of_nonneg_left hδ hn.le

/-- Multiplying phases adds their real angles. -/
theorem phase_mul (θ φ : ℝ) :
    Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * φ) =
      Complex.exp (Complex.I * ((θ + φ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugating the second phase changes the angular sum into a difference. -/
theorem phase_mul_conj (θ φ : ℝ) :
    Complex.exp (Complex.I * θ) * conj (Complex.exp (Complex.I * φ)) =
      Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

/-- The mixed kernel error at the degree and separation scales of the manuscript. -/
theorem crossRadialIndexKernel_bound_of_degree (N j : ℕ) (hN : 0 < N)
    (K r s t : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖(t : Real.Angle)‖) :
    ‖crossRadialIndexKernel N j r s (Complex.exp (Complex.I * t))‖ ≤
      Real.exp (-4 * K) / 640 := by
  have hsep := degree_times_separation_lower N hN (6400 * Real.exp (8 * K))
    ‖(t : Real.Angle)‖ (by positivity) hdegree hangle
  have hden : 0 < (N : ℝ) * ‖(t : Real.Angle)‖ := lt_of_lt_of_le (by positivity) hsep
  have ht : (t : Real.Angle) ≠ 0 := by intro he; simp [he] at hden
  exact (crossRadialIndexKernel_bound N j hN K r s t hK hr0 hs0 hr hs ht).trans
    (annular_kernel_error_le K _ hden hsep)

/-- Two separated annular jets have covariance lower bound `λ_K/2`.
The four angular conditions remove the two real-axis resonances and both
the ordinary and conjugate diagonals. -/
theorem paired_annular_jet_nondegeneracy (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (u v p q : ℂ) :
    (Real.exp (-4 * K) / 160) * (‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2)) ≤
      pairedJetCovarianceForm N r s (Complex.exp (Complex.I * θ))
        (Complex.exp (Complex.I * φ)) u v p q := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hr := annular_jet_nondegeneracy_of_degree N hN K r θ hK hNK hrl hru hdegree hθ u v
  have hs := annular_jet_nondegeneracy_of_degree N hN K s φ hK hNK hsl hsu hdegree hφ p q
  have hminus (j : ℕ) (_ : j ≤ 2) :
      ‖crossRadialIndexKernel N j r s
        (Complex.exp (Complex.I * θ) * conj (Complex.exp (Complex.I * φ)))‖ ≤
      Real.exp (-4 * K) / 640 := by
    rw [phase_mul_conj]
    exact crossRadialIndexKernel_bound_of_degree N j hN K r s (θ - φ) hK hr0 hs0 hru hsu hdegree hdifference
  have hplus (j : ℕ) (_ : j ≤ 2) :
      ‖crossRadialIndexKernel N j r s
        (Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * φ))‖ ≤
      Real.exp (-4 * K) / 640 := by
    rw [phase_mul]
    exact crossRadialIndexKernel_bound_of_degree N j hN K r s (θ + φ) hK hr0 hs0 hru hsu hdegree hsum
  have hcross := abs_crossJetCovarianceForm_le N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)) u v p q
    (Real.exp (-4 * K) / 640) (by positivity) hminus hplus
  have hcross' : |crossJetCovarianceForm N r s
      (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)) u v p q| ≤
      (Real.exp (-4 * K) / 80) / 4 *
        (‖u‖ ^ 2 + ‖v‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2)) := by
    refine hcross.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith [Real.exp_pos (-4 * K)]
  simpa only [div_div, show (80 : ℝ) * 2 = 160 by norm_num] using
    pairedJetCovarianceForm_lower N r s (Complex.exp (Complex.I * θ))
      (Complex.exp (Complex.I * φ)) u v p q (Real.exp (-4 * K) / 80) hr hs hcross'

/-- The paired real covariance in the coordinate order of the two value-derivative jets. -/
def realPairedJetCovarianceForm (N : ℕ) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
    (r ^ k * (((x 0 + (k : ℝ) / N * x 2) * (z ^ k).re) +
      ((x 1 + (k : ℝ) / N * x 3) * (z ^ k).im)) +
    s ^ k * (((x 4 + (k : ℝ) / N * x 6) * (w ^ k).re) +
      ((x 5 + (k : ℝ) / N * x 7) * (w ^ k).im))) ^ 2

/-- Four complex coefficients parametrize the paired eight-dimensional real form. -/
theorem realPairedJetCovarianceForm_eq_complex (N : ℕ) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    realPairedJetCovarianceForm N r s z w x = pairedJetCovarianceForm N r s z w
      ⟨x 0, -x 1⟩ ⟨x 2, -x 3⟩ ⟨x 4, -x 5⟩ ⟨x 6, -x 7⟩ := by
  unfold realPairedJetCovarianceForm pairedJetCovarianceForm
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The complex parametrization of paired directions preserves the Euclidean norm. -/
theorem paired_jet_coefficients_norm (x : EuclideanSpace ℝ (Fin 8)) :
    ‖(⟨x 0, -x 1⟩ : ℂ)‖ ^ 2 + ‖(⟨x 2, -x 3⟩ : ℂ)‖ ^ 2 +
      (‖(⟨x 4, -x 5⟩ : ℂ)‖ ^ 2 + ‖(⟨x 6, -x 7⟩ : ℂ)‖ ^ 2) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Complex.sq_norm, Complex.normSq_mk]
  norm_num
  ring

/-- The separated-pair nondegeneracy bound on native eight-dimensional real Euclidean space. -/
theorem real_paired_annular_jet_nondegeneracy (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    (Real.exp (-4 * K) / 160) * ‖x‖ ^ 2 ≤ realPairedJetCovarianceForm N r s
      (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)) x := by
  rw [realPairedJetCovarianceForm_eq_complex, ← paired_jet_coefficients_norm x]
  exact paired_annular_jet_nondegeneracy N hN K r s θ φ hK hNK hrl hru hsl hsu
    hdegree hθ hφ hdifference hsum _ _ _ _

end Erdos522

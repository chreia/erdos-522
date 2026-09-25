/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.Covariance.IndexMoments
import Erdos522.Probability.Covariance.OscillatorySums
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nondegeneracy of polynomial value and derivative jets

The covariance form of a normalized Rademacher jet splits into a radial
moment form and an oscillatory correction. The radial form is positive by
the affine grid-energy bound. Abel summation controls the correction away
from the real axis.
-/

noncomputable section
open scoped BigOperators
namespace Erdos522

/-- A complex affine function inherits both real grid-energy lower bounds. -/
theorem weighted_complex_affine_energy_lower (N : ℕ) (hN : 0 < N) (w : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hw : ∀ k ≤ N, c ≤ w k) (u v : ℂ) :
    c * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 16 ≤
      (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        w k * ‖u + ((k : ℝ) / N : ℝ) * v‖ ^ 2 := by
  have hre := weighted_index_energy_lower N hN w c hc hw u.re v.re
  have him := weighted_index_energy_lower N hN w c hc hw u.im v.im
  have he (k : ℕ) : ‖u + ((k : ℝ) / N : ℝ) * v‖ ^ 2 =
      (u.re + (k : ℝ) / N * v.re) ^ 2 + (u.im + (k : ℝ) / N * v.im) ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp_rw [he, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- The real projection of a complex number separates into circular and
oscillatory quadratic terms. -/
theorem real_projection_square (w : ℂ) :
    2 * w.re ^ 2 = ‖w‖ ^ 2 + (w ^ 2).re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/-- The radial-index Fourier kernel in the covariance expansion. -/
def radialIndexKernel (N j : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  (1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
    ((r ^ (2 * k) * ((k : ℝ) / N) ^ j : ℝ) : ℂ) * z ^ k

/-- The covariance quadratic form of `(f/√N, zf'/N^{3/2})`, expressed
using two complex coefficients for its four real coordinates. -/
def jetCovarianceForm (N : ℕ) (r : ℝ) (z u v : ℂ) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
    r ^ (2 * k) * (((u + ((k : ℝ) / N : ℝ) * v) * z ^ k).re) ^ 2

/-- Expanding an affine square uses exactly the first three radial-index kernels. -/
theorem affine_square_kernel (N : ℕ) (r : ℝ) (z u v : ℂ) :
    (1 / (N : ℂ)) * ∑ k ∈ Finset.range (N + 1),
      (r ^ (2 * k) : ℝ) * (u + ((k : ℝ) / N : ℝ) * v) ^ 2 * z ^ k =
      u ^ 2 * radialIndexKernel N 0 r z +
        (2 * u * v) * radialIndexKernel N 1 r z +
        v ^ 2 * radialIndexKernel N 2 r z := by
  unfold radialIndexKernel
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- The circular and oscillatory parts of the jet covariance form. -/
theorem jetCovarianceForm_decomposition (N : ℕ) (r : ℝ) (z u v : ℂ) (hz : ‖z‖ = 1) :
    2 * jetCovarianceForm N r z u v =
      (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1),
        r ^ (2 * k) * ‖u + ((k : ℝ) / N : ℝ) * v‖ ^ 2 +
      (u ^ 2 * radialIndexKernel N 0 r (z ^ 2) +
        (2 * u * v) * radialIndexKernel N 1 r (z ^ 2) +
        v ^ 2 * radialIndexKernel N 2 r (z ^ 2)).re := by
  rw [← affine_square_kernel]
  have real_mul_re (a : ℝ) (b : ℂ) : ((a : ℂ) * b).re = a * b.re := by simp
  have hpoint (k : ℕ) :
      2 * (r ^ (2 * k) * (((u + ((k : ℝ) / N : ℝ) * v) * z ^ k).re) ^ 2) =
        r ^ (2 * k) * ‖u + ((k : ℝ) / N : ℝ) * v‖ ^ 2 +
        ((r ^ (2 * k) : ℝ) * (u + ((k : ℝ) / N : ℝ) * v) ^ 2 * (z ^ 2) ^ k).re := by
    have h := real_projection_square ((u + ((k : ℝ) / N : ℝ) * v) * z ^ k)
    simp only [norm_mul, norm_pow, hz, one_pow, mul_one, mul_pow,
      ← pow_mul, mul_comm k 2] at h
    rw [mul_assoc ((r ^ (2 * k) : ℝ) : ℂ), real_mul_re, ← pow_mul]
    nlinarith [congrArg (fun t : ℝ => r ^ (2 * k) * t) h]
  have hscale (w : ℂ) : ((1 / (N : ℂ)) * w).re = (1 / (N : ℝ)) * w.re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
    exact real_mul_re _ _
  rw [hscale, Complex.re_sum, ← mul_add, ← Finset.sum_add_distrib]
  simp_rw [← hpoint]
  rw [← Finset.mul_sum]
  unfold jetCovarianceForm
  ring

/-- Three kernel bounds control every oscillatory affine quadratic form. -/
theorem norm_affine_quadratic_kernel_le (u v A B C : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : ‖A‖ ≤ ε) (hB : ‖B‖ ≤ ε) (hC : ‖C‖ ≤ ε) :
    ‖u ^ 2 * A + (2 * u * v) * B + v ^ 2 * C‖ ≤
      2 * ε * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  calc
    _ ≤ ‖u ^ 2 * A‖ + ‖(2 * u * v) * B‖ + ‖v ^ 2 * C‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖u‖ ^ 2 * ε + (2 * ‖u‖ * ‖v‖) * ε + ‖v‖ ^ 2 * ε := by
      simp only [norm_mul, norm_pow, Complex.norm_two]
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hε (sq_nonneg (‖u‖ - ‖v‖))]

/-- A radial energy lower bound and three Fourier bounds imply nondegeneracy
of the four-dimensional real jet covariance. -/
theorem jetCovarianceForm_lower (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (hz : ‖z‖ = 1) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hr : ∀ k ≤ N, c ≤ r ^ (2 * k))
    (hkernel : ∀ j ≤ 2, ‖radialIndexKernel N j r (z ^ 2)‖ ≤ ε) (u v : ℂ) :
    (c / 32 - ε) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ jetCovarianceForm N r z u v := by
  have henergy := weighted_complex_affine_energy_lower N hN
    (fun k => r ^ (2 * k)) c hc hr u v
  have hosc := norm_affine_quadratic_kernel_le u v
    (radialIndexKernel N 0 r (z ^ 2)) (radialIndexKernel N 1 r (z ^ 2))
    (radialIndexKernel N 2 r (z ^ 2)) ε hε
    (hkernel 0 (by omega)) (hkernel 1 (by omega)) (hkernel 2 le_rfl)
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (u ^ 2 * radialIndexKernel N 0 r (z ^ 2) +
      (2 * u * v) * radialIndexKernel N 1 r (z ^ 2) +
      v ^ 2 * radialIndexKernel N 2 r (z ^ 2)))).1
  have heq := jetCovarianceForm_decomposition N r z u v hz
  nlinarith

/-- The radial kernel is bounded by the inverse distance to the angular resonance. -/
theorem radialIndexKernel_bound (N j : ℕ) (hN : 0 < N) (K r t : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r ≤ 1 + K / N)
    (ht : (t : Real.Angle) ≠ 0) :
    ‖radialIndexKernel N j r (Complex.exp (Complex.I * t))‖ ≤
      10 * Real.exp (4 * K) / ((N : ℝ) * ‖(t : Real.Angle)‖) := by
  have h := normalized_radial_index_sum_le_angle_norm N j hN K r r t hK hr0 hr0 hr hr ht
  simpa only [radialIndexKernel, mul_pow, ← pow_add, ← two_mul] using h

/-- The annular radial weights have the square-power lower bound. -/
theorem radial_square_power_lower (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (K r : ℝ) (hK : 0 ≤ K) (hNK : 2 * K ≤ N) (hr0 : 0 ≤ r)
    (hrl : 1 - K / N ≤ r) : Real.exp (-4 * K) ≤ r ^ (2 * k) := by
  have h := radial_power_lower N k hN hk K r hK hNK hrl
  calc
    Real.exp (-4 * K) = Real.exp (-2 * K) * Real.exp (-2 * K) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ r ^ k * r ^ k := mul_le_mul h h (Real.exp_nonneg _) (pow_nonneg hr0 k)
    _ = r ^ (2 * k) := by rw [← pow_add]; congr 1; omega

/-- A separation threshold gives the required relative covariance error. -/
theorem annular_kernel_error_le (K D : ℝ) (hD : 0 < D)
    (hsep : 6400 * Real.exp (8 * K) ≤ D) :
    10 * Real.exp (4 * K) / D ≤ Real.exp (-4 * K) / 640 := by
  apply (div_le_iff₀ hD).mpr
  have hexp : Real.exp (-4 * K) * Real.exp (8 * K) = Real.exp (4 * K) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    10 * Real.exp (4 * K) =
        (Real.exp (-4 * K) / 640) * (6400 * Real.exp (8 * K)) := by
      rw [← hexp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsep (by positivity)

/-- Squaring a Fourier phase doubles its angle. -/
theorem phase_square (θ : ℝ) :
    Complex.exp (Complex.I * θ) ^ 2 = Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Away from the real-axis resonance, the normalized jet has the explicit
four-dimensional covariance lower bound `exp (-4K) / 80`. -/
theorem annular_jet_nondegeneracy (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsep : 6400 * Real.exp (8 * K) ≤ (N : ℝ) * ‖((2 * θ : ℝ) : Real.Angle)‖)
    (u v : ℂ) :
    (Real.exp (-4 * K) / 80) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
      jetCovarianceForm N r (Complex.exp (Complex.I * θ)) u v := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hden : 0 < (N : ℝ) * ‖((2 * θ : ℝ) : Real.Angle)‖ :=
    lt_of_lt_of_le (by positivity) hsep
  have ht : ((2 * θ : ℝ) : Real.Angle) ≠ 0 := by
    intro he
    simp [he] at hden
  let ε := 10 * Real.exp (4 * K) / ((N : ℝ) * ‖((2 * θ : ℝ) : Real.Angle)‖)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεsmall : ε ≤ Real.exp (-4 * K) / 640 := annular_kernel_error_le K _ hden hsep
  have hrad (k : ℕ) (hk : k ≤ N) : Real.exp (-4 * K) ≤ r ^ (2 * k) :=
    radial_square_power_lower N k hN hk K r hK hNK hr0 hrl
  have hkernel (j : ℕ) (_ : j ≤ 2) :
      ‖radialIndexKernel N j r (Complex.exp (Complex.I * θ) ^ 2)‖ ≤ ε := by
    simpa only [phase_square, ε] using
      radialIndexKernel_bound N j hN K r (2 * θ) hK hr0 hru ht
  have h := jetCovarianceForm_lower N hN r (Complex.exp (Complex.I * θ))
    (Complex.norm_exp_I_mul_ofReal θ) (Real.exp (-4 * K)) ε (Real.exp_nonneg _) hε hrad hkernel u v
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith [Real.exp_pos (-4 * K)]

/-- The degree and angular thresholds used for annular jet nondegeneracy. -/
theorem annular_jet_nondegeneracy_of_degree (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖) (u v : ℂ) :
    (Real.exp (-4 * K) / 80) * (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
      jetCovarianceForm N r (Complex.exp (Complex.I * θ)) u v := by
  apply annular_jet_nondegeneracy N hN K r θ hK hNK hrl hru _ u v
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  have hbound : 6400 * Real.exp (8 * K) ≤ Real.sqrt N := by nlinarith [Real.exp_pos (8 * K)]
  calc
    6400 * Real.exp (8 * K) ≤ Real.sqrt N := hbound
    _ = (N : ℝ) * (1 / Real.sqrt N) := by
      rw [mul_one_div]
      apply (eq_div_iff hs.ne').mpr
      simpa only [pow_two] using hsq
    _ ≤ _ := mul_le_mul_of_nonneg_left hangle hn.le

/-- The real covariance form, in the coordinate order
`(Re f, Im f, Re (zf'/N), Im (zf'/N)) / √N`. -/
def realJetCovarianceForm (N : ℕ) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (1 / (N : ℝ)) * ∑ k ∈ Finset.range (N + 1), r ^ (2 * k) *
    (((x 0 + (k : ℝ) / N * x 2) * (z ^ k).re) +
      ((x 1 + (k : ℝ) / N * x 3) * (z ^ k).im)) ^ 2

/-- Complex coefficients are a real-linear parametrization of the four-dimensional form. -/
theorem realJetCovarianceForm_eq_complex (N : ℕ) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    realJetCovarianceForm N r z x =
      jetCovarianceForm N r z ⟨x 0, -x 1⟩ ⟨x 2, -x 3⟩ := by
  unfold realJetCovarianceForm jetCovarianceForm
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The parametrization of the real jet form preserves its Euclidean norm. -/
theorem jet_coefficients_norm (x : EuclideanSpace ℝ (Fin 4)) :
    ‖(⟨x 0, -x 1⟩ : ℂ)‖ ^ 2 + ‖(⟨x 2, -x 3⟩ : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp only [Complex.sq_norm, Complex.normSq_mk]
  ring

/-- Annular nondegeneracy as a lower bound on a native four-dimensional
real Euclidean quadratic form. -/
theorem real_annular_jet_nondegeneracy (N : ℕ) (hN : 0 < N) (K r θ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hangle : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 4)) :
    (Real.exp (-4 * K) / 80) * ‖x‖ ^ 2 ≤
      realJetCovarianceForm N r (Complex.exp (Complex.I * θ)) x := by
  rw [realJetCovarianceForm_eq_complex, ← jet_coefficients_norm x]
  exact annular_jet_nondegeneracy_of_degree N hN K r θ hK hNK hrl hru hdegree hangle _ _

end Erdos522

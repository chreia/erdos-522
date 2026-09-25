/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Basic.PolynomialPrefixes

/-!
# Scalar normalization and polynomial zeros

Multiplying all coefficients by one nonzero scalar preserves the root
multiset, hence every regional count with multiplicity.
-/

noncomputable section
open Polynomial
namespace Erdos522

theorem polynomialPrefix_mul_coefficients (a : ℂ) (ξ c : ℕ → ℂ) (N : ℕ) :
    polynomialPrefix (fun k => a * ξ k) c N = C a * polynomialPrefix ξ c N := by
  ext k
  simp only [polynomialPrefix_coeff, coeff_C_mul]
  split_ifs <;> ring

/-- Nonzero scalar multiplication preserves every multiplicity-counted regional count. -/
theorem zeroCountIn_C_mul (P : ℂ[X]) {a : ℂ} (ha : a ≠ 0) (s : Set ℂ) :
    zeroCountIn (C a * P) s = zeroCountIn P s := by
  unfold zeroCountIn
  rw [roots_C_mul P ha]

theorem closedZeroCount_C_mul (P : ℂ[X]) {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    closedZeroCount (C a * P) r = closedZeroCount P r :=
  zeroCountIn_C_mul P ha _

/-- Scalar normalization preserves all prefix root counts, including zero prefixes. -/
theorem closedZeroCount_prefix_mul_coefficients {a : ℂ} (ha : a ≠ 0)
    (ξ c : ℕ → ℂ) (N : ℕ) (r : ℝ) :
    closedZeroCount (polynomialPrefix (fun k => a * ξ k) c N) r =
      closedZeroCount (polynomialPrefix ξ c N) r := by
  rw [polynomialPrefix_mul_coefficients, closedZeroCount_C_mul _ ha]

end Erdos522

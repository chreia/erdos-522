/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.GaussianProducts

/-!
# Small-value events at separated points

The ordinary and conjugate angular separations bound the off-diagonal
covariance. Gaussian comparison and the two convex-set approximations then
control the dependence of the two polynomial jet events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace ComplexConjugate

namespace Erdos522

/-- Matrix and covariance-form descriptions of the actual one-point jet agree. -/
theorem quadratic_signCovarianceMatrix_jet (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    x.ofLp ⬝ᵥ signCovarianceMatrix (realJetCoefficient N r z) *ᵥ x.ofLp =
      realJetCovarianceForm N r z x := by
  change x.ofLp ⬝ᵥ covarianceMatrix ((LogMoments.signMeasure N).map (realRademacherJet N r z)) *ᵥ x.ofLp = _
  rw [dotProduct_covarianceMatrix_mulVec, covarianceBilin_realRademacherJet N hN]

/-- Matrix and covariance-form descriptions of the actual paired jet agree. -/
theorem quadratic_signCovarianceMatrix_pairedJet (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ signCovarianceMatrix (realPairedJetCoefficient N r s z w) *ᵥ x.ofLp =
      realPairedJetCovarianceForm N r s z w x := by
  change x.ofLp ⬝ᵥ covarianceMatrix
    ((LogMoments.signMeasure N).map (realPairedRademacherJet N r s z w)) *ᵥ x.ofLp = _
  rw [dotProduct_covarianceMatrix_mulVec, covarianceBilin_realPairedRademacherJet N hN]

/-- The difference between the actual paired covariance and its independent block
reference is exactly twice the mixed form. -/
theorem pairedJet_covariance_error_eq (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (x : EuclideanSpace ℝ (Fin 8)) :
    x.ofLp ⬝ᵥ (signCovarianceMatrix (realPairedJetCoefficient N r s z w) -
      gaussianBlockCovariance (signCovarianceMatrix (realJetCoefficient N r z))
        (signCovarianceMatrix (realJetCoefficient N s w))) *ᵥ x.ofLp =
      2 * crossJetCovarianceForm N r s z w
        ⟨x 0, -x 1⟩ ⟨x 2, -x 3⟩ ⟨x 4, -x 5⟩ ⟨x 6, -x 7⟩ := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadratic_signCovarianceMatrix_pairedJet N hN,
    quadratic_gaussianBlockCovariance (m := 4) (n := 4), quadratic_signCovarianceMatrix_jet N hN,
    quadratic_signCovarianceMatrix_jet N hN, realPairedJetCovarianceForm_eq_complex,
    realJetCovarianceForm_eq_complex, realJetCovarianceForm_eq_complex,
    pairedJetCovarianceForm_decomposition]
  have hfirst : (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).1 =
      toLp 2 ![x 0, x 1, x 2, x 3] := by ext i; fin_cases i <;> rfl
  have hsecond : (EuclideanSpace.finAddEquivProd (n := 4) (m := 4) x).2 =
      toLp 2 ![x 4, x 5, x 6, x 7] := by ext i; fin_cases i <;> rfl
  rw [hfirst, hsecond]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Inverse-square-root angular separation bounds each mixed kernel at that scale. -/
theorem crossRadialIndexKernel_bound_sqrt (N j : ℕ) (hN : 0 < N)
    (K r s t : ℝ) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (hangle : 1 / Real.sqrt N ≤ ‖(t : Real.Angle)‖) :
    ‖crossRadialIndexKernel N j r s (Complex.exp (Complex.I * t))‖ ≤
      10 * Real.exp (4 * K) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsep := degree_times_separation_lower N hN (Real.sqrt N) ‖(t : Real.Angle)‖
    hsqrt.le (by rw [Real.sq_sqrt hn.le]) hangle
  have hden : 0 < (N : ℝ) * ‖(t : Real.Angle)‖ := hsqrt.trans_le hsep
  have ht : (t : Real.Angle) ≠ 0 := by intro ht; simp [ht] at hden
  exact (crossRadialIndexKernel_bound N j hN K r s t hK hr0 hs0 hr hs ht).trans
    (div_le_div_of_nonneg_left (by positivity) hsqrt hsep)

/-- The paired covariance differs from independent marginals by at most
`20 exp(4K)/sqrt N` as a quadratic form. -/
theorem pairedJet_covariance_error_le (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : r ≤ 1 + K / N) (hs : s ≤ 1 + K / N)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (x : EuclideanSpace ℝ (Fin 8)) :
    |x.ofLp ⬝ᵥ (signCovarianceMatrix (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))) -
      gaussianBlockCovariance
        (signCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ))))
        (signCovarianceMatrix (realJetCoefficient N s (Complex.exp (Complex.I * φ))))) *ᵥ x.ofLp| ≤
      (20 * Real.exp (4 * K) / Real.sqrt N) * ‖x‖ ^ 2 := by
  have hminus (j : ℕ) (_ : j ≤ 2) :
      ‖crossRadialIndexKernel N j r s
        (Complex.exp (Complex.I * θ) * conj (Complex.exp (Complex.I * φ)))‖ ≤
        10 * Real.exp (4 * K) / Real.sqrt N := by
    rw [phase_mul_conj]
    exact crossRadialIndexKernel_bound_sqrt N j hN K r s (θ - φ) hK hr0 hs0 hr hs hdifference
  have hplus (j : ℕ) (_ : j ≤ 2) :
      ‖crossRadialIndexKernel N j r s
        (Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * φ))‖ ≤
        10 * Real.exp (4 * K) / Real.sqrt N := by
    rw [phase_mul]
    exact crossRadialIndexKernel_bound_sqrt N j hN K r s (θ + φ) hK hr0 hs0 hr hs hsum
  have h := abs_crossJetCovarianceForm_le N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))
    ⟨x 0, -x 1⟩ ⟨x 2, -x 3⟩ ⟨x 4, -x 5⟩ ⟨x 6, -x 7⟩
    (10 * Real.exp (4 * K) / Real.sqrt N) (by positivity) hminus hplus
  rw [paired_jet_coefficients_norm] at h
  rw [pairedJet_covariance_error_eq N hN, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ((10 * Real.exp (4 * K) / Real.sqrt N) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- The angular degree threshold makes the relative covariance perturbation at most one half. -/
theorem pairedJet_relative_error_le_half (N : ℕ) (hN : 0 < N) (K : ℝ)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ)) :
    (20 * Real.exp (4 * K) / Real.sqrt N) / (Real.exp (-4 * K) / 80) ≤ 1 / 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have he : 0 < Real.exp (-4 * K) := Real.exp_pos _
  have hsq := Real.sq_sqrt hn.le
  have hslo : 6400 * Real.exp (8 * K) ≤ Real.sqrt N := by
    nlinarith [Real.exp_pos (8 * K)]
  have hexp : Real.exp (8 * K) * Real.exp (-4 * K) = Real.exp (4 * K) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_iff₀ (div_pos he (by norm_num))).mpr
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_le_mul_of_nonneg_right hslo he.le]

/-- The Gaussian law of separated polynomial jets differs from its independent
marginals by at most the manuscript's explicit covariance-comparison constant. -/
theorem gaussian_pairedJet_measureReal_prod_le (N : ℕ) (hN : 0 < N) (K r s θ φ : ℝ)
    (hK : 0 ≤ K) (hNK : 2 * K ≤ N)
    (hrl : 1 - K / N ≤ r) (hru : r ≤ 1 + K / N)
    (hsl : 1 - K / N ≤ s) (hsu : s ≤ 1 + K / N)
    (hdegree : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
    (hθ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
    (hφ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
    (hdifference : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
    (hsum : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
    (A B : Set (EuclideanSpace ℝ (Fin 4))) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(multivariateGaussian 0 (signCovarianceMatrix (realPairedJetCoefficient N r s
        (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
      (multivariateGaussian 0 (signCovarianceMatrix (realJetCoefficient N r
        (Complex.exp (Complex.I * θ))))).real A *
      (multivariateGaussian 0 (signCovarianceMatrix (realJetCoefficient N s
        (Complex.exp (Complex.I * φ))))).real B| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  let S₁ := signCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
  let S₂ := signCovarianceMatrix (realJetCoefficient N s (Complex.exp (Complex.I * φ)))
  let S := signCovarianceMatrix (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))
  let c := Real.exp (-4 * K) / 80
  let δ := 20 * Real.exp (4 * K) / Real.sqrt N
  have hc : 0 < c := by dsimp [c]; positivity
  have h₁ : S₁.PosDef := realJetCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hθ
  have h₂ : S₂.PosDef := realJetCovarianceMatrix_posDef N hN K s φ hK hNK hsl hsu hdegree hφ
  have hl₁ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₁ *ᵥ x.ofLp := by
    rw [quadratic_signCovarianceMatrix_jet N hN]
    exact real_annular_jet_nondegeneracy N hN K r θ hK hNK hrl hru hdegree hθ x
  have hl₂ (x : EuclideanSpace ℝ (Fin 4)) : c * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S₂ *ᵥ x.ofLp := by
    rw [quadratic_signCovarianceMatrix_jet N hN]
    exact real_annular_jet_nondegeneracy N hN K s φ hK hNK hsl hsu hdegree hφ x
  have hS : S.PosDef := realPairedJetCovarianceMatrix_posDef N hN K r s θ φ hK hNK
    hrl hru hsl hsu hdegree hθ hφ hdifference hsum
  have hT := gaussianBlockCovariance_posDef_of_lower S₁ S₂ h₁.posSemidef h₂.posSemidef c hc hl₁ hl₂
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : K / (N : ℝ) ≤ 1 / 2 := (div_le_iff₀ hn).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 ≤ s := by linarith
  have herror := pairedJet_covariance_error_le N hN K r s θ φ hK hr0 hs0 hru hsu hdifference hsum
  have h := gaussian_measureReal_sub_le_eight S (gaussianBlockCovariance S₁ S₂) hS hT c δ hc
    (by dsimp [δ]; positivity) (pairedJet_relative_error_le_half N hN K hdegree)
    (gaussianBlockCovariance_lower S₁ S₂ c hl₁ hl₂) herror
    ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) ((hA.prod hB).preimage (by fun_prop))
  rw [gaussianBlockCovariance_measureReal_prod S₁ S₂ h₁.posSemidef h₂.posSemidef A B hA hB] at h
  refine h.trans ?_
  dsimp [c, δ]
  have hpos : 0 ≤ Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N) := by positivity
  calc
    _ = 40 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by ring
    _ ≤ 80 * (Real.exp (4 * K) / ((Real.exp (-4 * K) / 80) * Real.sqrt N)) := by nlinarith
    _ = _ := by ring

local instance {d : ℕ} : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.ConvexSpace.ofModule
local instance {d : ℕ} : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin d)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- The concatenated preimage of a convex rectangle is convex. -/
theorem isConvexSet_pair_preimage (A B : Set (EuclideanSpace ℝ (Fin 4)))
    (hA : Convexity.IsConvexSet ℝ A) (hB : Convexity.IsConvexSet ℝ B) :
    Convexity.IsConvexSet ℝ
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) :=
  (hA.prod hB).preimage (Convexity.IsAffineMap.linearMap EuclideanSpace.finAddEquivProd.toLinearMap)

/-- Products of numbers in the unit interval change by at most the sum of the changes. -/
theorem abs_mul_sub_mul_le_of_unitInterval (a b c d : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = a * |b - d| + |a - c| * d := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hd]
    _ ≤ |a - c| + |b - d| := by nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

/-- Approximate factorization for arbitrary measurable convex events in two
separated normalized Rademacher jets. -/
theorem exists_annular_jet_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖)
      (A B : Set (EuclideanSpace ℝ (Fin 4)))
      (_ : MeasurableSet A) (_ : MeasurableSet B)
      (_ : Convexity.IsConvexSet ℝ A) (_ : Convexity.IsConvexSet ℝ B),
      |((LogMoments.signMeasure N).map (realPairedRademacherJet N r s
          (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real
        ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)) -
        ((LogMoments.signMeasure N).map (realRademacherJet N r
          (Complex.exp (Complex.I * θ)))).real A *
        ((LogMoments.signMeasure N).map (realRademacherJet N s
          (Complex.exp (Complex.I * φ)))).real B| ≤
        (2 * jetGaussianErrorConstant C K + pairedJetGaussianErrorConstant C K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_gaussian_approximation_annular_jet_constant
  obtain ⟨C₂, hC₂, h₂⟩ := exists_gaussian_approximation_paired_annular_jet_constant
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum A B hA hB hcA hcB
  let E := (EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹' (A ×ˢ B)
  have hE : MeasurableSet E := (hA.prod hB).preimage (by fun_prop)
  have hcE : Convexity.IsConvexSet ℝ E := isConvexSet_pair_preimage A B hcA hcB
  have hmono₁ : jetGaussianErrorConstant C₁ K ≤ jetGaussianErrorConstant (C₁ + C₂) K := by
    unfold jetGaussianErrorConstant
    gcongr
    linarith
  have hmono₂ : pairedJetGaussianErrorConstant C₂ K ≤ pairedJetGaussianErrorConstant (C₁ + C₂) K := by
    unfold pairedJetGaussianErrorConstant
    gcongr
    linarith
  have hb₁ := (h₁ N hN K r θ hK hNK hrl hru hdegree hθ A hA hcA).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hb₂ := (h₁ N hN K s φ hK hNK hsl hsu hdegree hφ B hB hcB).trans
    (div_le_div_of_nonneg_right hmono₁ (Real.sqrt_nonneg N))
  have hpair := (h₂ N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree
    hθ hφ hdifference hsum E hE hcE).trans
    (div_le_div_of_nonneg_right hmono₂ (Real.sqrt_nonneg N))
  let p₁ := ((LogMoments.signMeasure N).map
    (realRademacherJet N r (Complex.exp (Complex.I * θ)))).real A
  let p₂ := ((LogMoments.signMeasure N).map
    (realRademacherJet N s (Complex.exp (Complex.I * φ)))).real B
  let g₁ := (multivariateGaussian 0 (signCovarianceMatrix
    (realJetCoefficient N r (Complex.exp (Complex.I * θ))))).real A
  let g₂ := (multivariateGaussian 0 (signCovarianceMatrix
    (realJetCoefficient N s (Complex.exp (Complex.I * φ))))).real B
  let p := ((LogMoments.signMeasure N).map (realPairedRademacherJet N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ)))).real E
  let g := (multivariateGaussian 0 (signCovarianceMatrix (realPairedJetCoefficient N r s
    (Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * φ))))).real E
  have hp₂ : p₂ ≤ 1 := measureReal_le_one
  have hg₁ : g₁ ≤ 1 := measureReal_le_one
  have hm := abs_mul_sub_mul_le_of_unitInterval g₁ g₂ p₁ p₂
    measureReal_nonneg hg₁ measureReal_nonneg hp₂
  have hb₁' : |g₁ - p₁| ≤ jetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    change |p₁ - g₁| ≤ _ at hb₁
    rwa [abs_sub_comm] at hb₁
  have hb₂' : |g₂ - p₂| ≤ jetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N := by
    change |p₂ - g₂| ≤ _ at hb₂
    rwa [abs_sub_comm] at hb₂
  have hg : |g - g₁ * g₂| ≤
      (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N :=
    gaussian_pairedJet_measureReal_prod_le N hN K r s θ φ hK hNK hrl hru hsl hsu
      hdegree hθ hφ hdifference hsum A B hA hB
  change |p - g| ≤ _ at hpair
  change |p - p₁ * p₂| ≤ _
  calc
    _ ≤ |p - g| + |g - g₁ * g₂| + |g₁ * g₂ - p₁ * p₂| := by
      calc
        _ ≤ |p - g| + |g - p₁ * p₂| := abs_sub_le _ _ _
        _ ≤ _ := by linarith [abs_sub_le g (g₁ * g₂) (p₁ * p₂)]
    _ ≤ pairedJetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
        (80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N +
        (jetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N +
          jetGaussianErrorConstant (C₁ + C₂) K / Real.sqrt N) :=
      add_le_add (add_le_add hpair hg) (hm.trans (add_le_add hb₁' hb₂'))
    _ = _ := by ring

/-- Splitting the paired vector recovers the two jets of the same sign polynomial. -/
theorem finAddEquivProd_realPairedRademacherJet (N : ℕ) (r s : ℝ) (z w : ℂ)
    (ω : LogMoments.SignVector N) :
    EuclideanSpace.finAddEquivProd (n := 4) (m := 4) (realPairedRademacherJet N r s z w ω) =
      (realRademacherJet N r z ω, realRademacherJet N s w ω) := by
  rw [realPairedRademacherJet_eq_normalizedPolynomialJetPair,
    realRademacherJet_eq_normalizedPolynomialJet, realRademacherJet_eq_normalizedPolynomialJet]
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

/-- Simultaneous closed value and radial derivative thresholds at a polynomial argument. -/
def polynomialJetSmallBallEvent (N : ℕ) (w : ℂ) (u v : ℝ) : Set (LogMoments.SignVector N) :=
  {ω | ‖(rademacherPolynomial N ω).eval w‖ ≤ u * Real.sqrt N ∧
    ‖w * (rademacherPolynomial N ω).derivative.eval w‖ ≤ v * ((N : ℝ) * Real.sqrt N)}

/-- The one-point jet law measures precisely the polynomial small-ball event. -/
theorem realJet_measureReal_smallBall (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ) (u v : ℝ) :
    ((LogMoments.signMeasure N).map (realRademacherJet N r z)).real (jetSmallBallSet u v) =
      (LogMoments.signMeasure N).real (polynomialJetSmallBallEvent N (r * z) u v) := by
  rw [measureReal_def, Measure.map_apply (measurable_of_finite _) (measurableSet_jetSmallBallSet u v)]
  congr 2
  ext ω
  exact mem_jetSmallBallSet_rademacher N hN r z ω u v

/-- The paired jet rectangle measures the intersection of the actual polynomial events. -/
theorem realPairedJet_measureReal_smallBall (N : ℕ) (hN : 0 < N) (r s : ℝ) (z w : ℂ)
    (u v u' v' : ℝ) :
    ((LogMoments.signMeasure N).map (realPairedRademacherJet N r s z w)).real
      ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
        (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) =
      (LogMoments.signMeasure N).real (polynomialJetSmallBallEvent N (r * z) u v ∩
        polynomialJetSmallBallEvent N (s * w) u' v') := by
  have hE : MeasurableSet ((EuclideanSpace.finAddEquivProd (n := 4) (m := 4)) ⁻¹'
      (jetSmallBallSet u v ×ˢ jetSmallBallSet u' v')) :=
    ((measurableSet_jetSmallBallSet u v).prod (measurableSet_jetSmallBallSet u' v')).preimage
      (by fun_prop)
  rw [measureReal_def, Measure.map_apply (measurable_of_finite _) hE]
  congr 2
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, finAddEquivProd_realPairedRademacherJet,
    mem_jetSmallBallSet_rademacher N hN, Set.mem_inter_iff, polynomialJetSmallBallEvent, Set.mem_ofPred_eq]

/-- Joint small-value events for a single Rademacher polynomial factor up to the
explicit inverse-square-root error at separated annular points. -/
theorem exists_annular_polynomial_small_ball_factorization_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r s θ φ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : 1 - K / N ≤ s) (_ : s ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((2 * φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ - φ : ℝ) : Real.Angle)‖)
      (_ : 1 / Real.sqrt N ≤ ‖((θ + φ : ℝ) : Real.Angle)‖) (u v u' v' : ℝ),
      |(LogMoments.signMeasure N).real
        (polynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v ∩
          polynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v') -
        (LogMoments.signMeasure N).real
          (polynomialJetSmallBallEvent N (r * Complex.exp (Complex.I * θ)) u v) *
        (LogMoments.signMeasure N).real
          (polynomialJetSmallBallEvent N (s * Complex.exp (Complex.I * φ)) u' v')| ≤
        (2 * jetGaussianErrorConstant C K + pairedJetGaussianErrorConstant C K +
          80 * Real.exp (4 * K) / (Real.exp (-4 * K) / 80)) / Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_annular_jet_factorization_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum u v u' v'
  have hb := h N hN K r s θ φ hK hNK hrl hru hsl hsu hdegree hθ hφ hdifference hsum
    (jetSmallBallSet u v) (jetSmallBallSet u' v')
    (measurableSet_jetSmallBallSet u v) (measurableSet_jetSmallBallSet u' v')
    (isConvexSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u' v')
  rwa [realPairedJet_measureReal_smallBall N hN, realJet_measureReal_smallBall N hN,
    realJet_measureReal_smallBall N hN] at hb

end Erdos522

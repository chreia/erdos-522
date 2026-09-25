/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.GaussianApproximation.PairedJets
import Erdos522.Probability.GaussianApproximation.DiagonalEntropy
import Erdos522.Probability.Covariance.JetEvaluation
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Small values of polynomial jets

Gaussian density bounds and convex-set approximation give the product scale
of the value and derivative thresholds for a normalized polynomial jet.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal MatrixOrder RealInnerProductSpace

namespace Erdos522

/-- The centered real Gaussian density is bounded by its value at the origin. -/
theorem gaussianReal_le_density_constant (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal 0 v ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) • volume := by
  rw [gaussianReal_of_var_ne_zero 0 hv, ← withDensity_const]
  apply withDensity_mono
  apply ae_of_all
  intro x
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))

/-- Uniform density domination multiplies under finite independent products. -/
theorem pi_le_constant_smul_volume (d : ℕ) (μ : Fin d → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (a : ℝ≥0)
    (hμ : ∀ i, μ i ≤ (a : ℝ≥0∞) • volume) :
    Measure.pi μ ≤ (a : ℝ≥0∞) ^ d • volume := by
  induction d with
  | zero =>
    rw [pow_zero, one_smul, Measure.pi_of_empty, Measure.volume_pi_eq_dirac]
  | succ d ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hsplit := measurePreserving_piFinSuccAbove μ 0
    have hvsplit := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have htail := ih (fun i => μ (Fin.succ i)) (fun i => hμ (Fin.succ i))
    calc
      Measure.pi μ = ((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))).map e.symm := by
        simpa [e] using hsplit.symm.map_eq.symm
      _ ≤ (((a : ℝ≥0∞) • volume).prod ((a : ℝ≥0∞) ^ d • volume)).map e.symm :=
        Measure.map_mono (Measure.prod_mono (hμ 0) htail) e.symm.measurable
      _ = (a : ℝ≥0∞) ^ (d + 1) • volume := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
          Measure.map_smul]
        rw [show (volume.prod volume).map e.symm = volume from hvsplit.symm.map_eq]
        rw [pow_succ, mul_comm]
        exact e.symm.measurable.aemeasurable

/-- An isotropic Gaussian on Euclidean space has a dimension-dependent density bound. -/
theorem isotropicGaussian_le_density_constant (d : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    multivariateGaussian 0 (Matrix.diagonal fun _ : Fin d => (v : ℝ)) ≤
      (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹)) ^ d • volume := by
  rw [← map_pi_gaussianReal_eq_multivariateGaussian]
  let a : ℝ≥0 := ⟨(Real.sqrt (2 * Real.pi * v))⁻¹, by positivity⟩
  have ha : (a : ℝ≥0∞) = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) :=
    by exact ENNReal.ofReal_coe_nnreal.symm
  have h := pi_le_constant_smul_volume d (fun _ => gaussianReal 0 v) a
    (fun _ => by
      rw [ha]
      exact gaussianReal_le_density_constant v hv)
  have hm := Measure.map_mono h (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
  change (Measure.pi fun _ : Fin d => gaussianReal 0 v).map (toLp 2) ≤
    ((a : ℝ≥0∞) ^ d • volume).map (toLp 2) at hm
  rw [Measure.map_smul, (PiLp.volume_preserving_toLp (Fin d)).map_eq] at hm
  · simpa only [ha] using hm
  · exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable

/-- Independent centered Gaussian sums add their covariance matrices. -/
theorem multivariateGaussian_covariance_add {d : ℕ}
    (S T : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)).map
        (fun p => p.1 + p.2) = multivariateGaussian 0 (S + T) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ (Fin d))
  ext x
  rw [charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hT, charFun_multivariateGaussian (hS.add hT),
    inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

/-- Adding independent noise preserves a uniform Lebesgue density bound. -/
theorem gaussian_add_preserves_density_bound {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℝ≥0∞) (hμ : μ ≤ a • volume) :
    (μ.prod ν).map (fun p => p.1 + p.2) ≤ a • volume := by
  have h := Measure.map_mono (Measure.prod_mono hμ (le_refl ν))
    (show Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) by fun_prop)
  rw [Measure.prod_smul_left, Measure.map_smul] at h
  · have hvol : MeasurePreserving (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2)
        (volume.prod ν) volume :=
      measurePreserving_fst.comp (measurePreserving_add_prod volume ν)
    rwa [hvol.map_eq] at h
  · fun_prop

/-- A scalar lower bound on a covariance leaves a positive semidefinite remainder. -/
theorem covariance_sub_diagonal_posSemidef {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (c : ℝ≥0)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d),
      (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    (S - Matrix.diagonal fun _ => (c : ℝ)).PosSemidef := by
  have hdiagHermitian : (Matrix.diagonal fun _ : Fin d => (c : ℝ)).IsHermitian :=
    (Matrix.PosSemidef.diagonal (fun _ => c.property)).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hS.isHermitian.sub hdiagHermitian)
  intro x
  have h := hlower (WithLp.toLp 2 x)
  have hdiag : x ⬝ᵥ (Matrix.diagonal fun _ : Fin d => (c : ℝ)) *ᵥ x =
      (c : ℝ) * ‖WithLp.toLp 2 x‖ ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hdiag]
  exact sub_nonneg.mpr h

/-- A Gaussian with covariance at least `c I` has density at most `(2πc)^(-d/2)`. -/
theorem multivariateGaussian_le_density_constant {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (c : ℝ≥0) (hc : c ≠ 0)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin d),
      (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    multivariateGaussian 0 S ≤
      (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * c))⁻¹)) ^ d • volume := by
  have hrem := covariance_sub_diagonal_posSemidef S hS c hlower
  have hdiag : (Matrix.diagonal fun _ : Fin d => (c : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun _ => c.property)
  have hsum := multivariateGaussian_covariance_add _ _ hdiag hrem
  rw [add_sub_cancel] at hsum
  rw [← hsum]
  exact gaussian_add_preserves_density_bound _ _ _ (isotropicGaussian_le_density_constant d c hc)

/-- A real four-dimensional jet is identified with its two complex coordinates. -/
def jetComplexCoordinates : EuclideanSpace ℝ (Fin 4) ≃ᵐ ℂ × ℂ :=
  (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.trans
    (((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))).trans
        (Complex.measurableEquivPi.symm.prodCongr Complex.measurableEquivPi.symm))

/-- The two complex coordinates are value followed by derivative. -/
theorem jetComplexCoordinates_apply (x : EuclideanSpace ℝ (Fin 4)) :
    jetComplexCoordinates x = (x 0 + x 1 * Complex.I, x 2 + x 3 * Complex.I) := by
  rfl

/-- The identification of a real jet with two complex coordinates preserves volume. -/
theorem volume_preserving_jetComplexCoordinates : MeasurePreserving jetComplexCoordinates := by
  exact (Complex.volume_preserving_equiv_pi.symm.prod
    Complex.volume_preserving_equiv_pi.symm).comp
      ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).comp
        ((volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
          (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.comp
          (PiLp.volume_preserving_ofLp (Fin 4))))

/-- The product of the closed value disk and closed derivative disk. -/
def jetSmallBallSet (u v : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) :=
  jetComplexCoordinates ⁻¹' (Metric.closedBall 0 u ×ˢ Metric.closedBall 0 v)

/-- Membership in the product of the two complex disks. -/
theorem mem_jetSmallBallSet (u v : ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    x ∈ jetSmallBallSet u v ↔
      ‖(x 0 : ℂ) + x 1 * Complex.I‖ ≤ u ∧ ‖(x 2 : ℂ) + x 3 * Complex.I‖ ≤ v := by
  simp only [jetSmallBallSet, Set.mem_preimage, jetComplexCoordinates_apply, Set.mem_prod,
    Metric.mem_closedBall, dist_zero_right]

/-- The closed jet small-ball event is measurable. -/
theorem measurableSet_jetSmallBallSet (u v : ℝ) : MeasurableSet (jetSmallBallSet u v) :=
  (measurableSet_closedBall.prod measurableSet_closedBall).preimage jetComplexCoordinates.measurable

/-- The exact two-disk volume gives the product scale of both thresholds. -/
theorem volume_jetSmallBallSet (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    volume (jetSmallBallSet u v) = ENNReal.ofReal (Real.pi ^ 2 * u ^ 2 * v ^ 2) := by
  rw [jetSmallBallSet, volume_preserving_jetComplexCoordinates.measure_preimage
    (measurableSet_closedBall.prod measurableSet_closedBall).nullMeasurableSet]
  change (volume.prod volume : Measure (ℂ × ℂ)) (Metric.closedBall 0 u ×ˢ Metric.closedBall 0 v) = _
  rw [Measure.prod_prod, Complex.volume_closedBall, Complex.volume_closedBall]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hu, ENNReal.ofReal_pow hv]
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [hpi]
  ring

/-- Every positive four-dimensional Gaussian jet obeys the exact two-disk density bound. -/
theorem gaussian_jetSmallBallSet_le (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hS : S.PosSemidef) (c : ℝ≥0) (hc : c ≠ 0)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin 4),
      (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤ u ^ 2 * v ^ 2 / (4 * (c : ℝ) ^ 2) := by
  have h := multivariateGaussian_le_density_constant S hS c hc hlower (jetSmallBallSet u v)
  rw [Measure.smul_apply, smul_eq_mul, volume_jetSmallBallSet u v hu hv] at h
  have hb : (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * c))⁻¹)) ^ 4 *
      ENNReal.ofReal (Real.pi ^ 2 * u ^ 2 * v ^ 2) =
      ENNReal.ofReal (u ^ 2 * v ^ 2 / (4 * (c : ℝ) ^ 2)) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hc' : (0 : ℝ) < c := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
    have hs : Real.sqrt (2 * Real.pi * c) ^ 2 = 2 * Real.pi * c := Real.sq_sqrt (by positivity)
    have hfour : Real.sqrt (2 * Real.pi * c) ^ 4 = (2 * Real.pi * c) ^ 2 := by nlinarith [sq_nonneg (Real.sqrt (2 * Real.pi * c) ^ 2 - 2 * Real.pi * c)]
    rw [inv_pow, hfour]
    field_simp
    ring
  rw [hb] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hnonneg : 0 ≤ u ^ 2 * v ^ 2 / (4 * (c : ℝ) ^ 2) := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at ht
  exact ht

/-- The value and derivative coordinate identification is real-linear. -/
def jetComplexLinearMap : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℂ × ℂ where
  toFun := jetComplexCoordinates
  map_add' x y := by
    simp only [jetComplexCoordinates_apply, PiLp.add_apply, Complex.ofReal_add]
    ext <;> simp <;> ring
  map_smul' a x := by
    simp only [jetComplexCoordinates_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ext <;> simp <;> ring

local instance : Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Convexity.ConvexSpace.ofModule
local instance : Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Convexity.IsModuleConvexSpace.of_module

/-- The two-disk event is a convex subset of real jet space. -/
theorem isConvexSet_jetSmallBallSet (u v : ℝ) : Convexity.IsConvexSet ℝ (jetSmallBallSet u v) := by
  have h : Convex ℝ (jetSmallBallSet u v) :=
    ((convex_closedBall (0 : ℂ) u).prod (convex_closedBall (0 : ℂ) v)).linear_preimage jetComplexLinearMap
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab x hx y hy
  simpa [Convexity.convexCombPair_eq_sum] using (convex_iff_add_mem.mp h) hx hy ha hb hab

/-- Uniform joint small-ball estimate for the normalized annular Rademacher jet. -/
theorem exists_annular_jet_small_ball_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r θ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v),
      ((LogMoments.signMeasure N).map
        (realRademacherJet N r (Complex.exp (Complex.I * θ)))).real (jetSmallBallSet u v) ≤
        u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) +
          jetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_approximation_annular_jet_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r θ hK hNK hrl hru hdegree hangle u v hu hv
  let S := signCovarianceMatrix (realJetCoefficient N r (Complex.exp (Complex.I * θ)))
  let c : ℝ≥0 := ⟨Real.exp (-4 * K) / 80, by positivity⟩
  have hc : c ≠ 0 := ne_of_gt (show 0 < c from by change 0 < Real.exp (-4 * K) / 80; positivity)
  have hS : S.PosDef := realJetCovarianceMatrix_posDef N hN K r θ hK hNK hrl hru hdegree hangle
  have hlower (x : EuclideanSpace ℝ (Fin 4)) : (c : ℝ) * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [show S = covarianceMatrix ((LogMoments.signMeasure N).map
      (realRademacherJet N r (Complex.exp (Complex.I * θ)))) from rfl,
      dotProduct_covarianceMatrix_mulVec]
    exact covarianceBilin_realRademacherJet_lower N hN K r θ hK hNK hrl hru hdegree hangle x
  have hg := gaussian_jetSmallBallSet_le S hS.posSemidef c hc hlower u v hu hv
  have hb := hbound N hN K r θ hK hNK hrl hru hdegree hangle (jetSmallBallSet u v)
    (measurableSet_jetSmallBallSet u v) (isConvexSet_jetSmallBallSet u v)
  have hb' := (le_abs_self _).trans hb
  change (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
    u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) at hg
  change ((LogMoments.signMeasure N).map
      (realRademacherJet N r (Complex.exp (Complex.I * θ)))).real (jetSmallBallSet u v) -
    (multivariateGaussian 0 S).real (jetSmallBallSet u v) ≤
      jetGaussianErrorConstant C K / Real.sqrt N at hb'
  linarith

/-- The complex coordinates of the normalized polynomial jet retain the exact denominators. -/
theorem jetComplexCoordinates_normalizedPolynomialJet (P : Polynomial ℂ) (N : ℕ) (w : ℂ) :
    jetComplexCoordinates (normalizedPolynomialJet P N w) =
      (P.eval w / (Real.sqrt N : ℂ),
        w * P.derivative.eval w / (((N : ℝ) * Real.sqrt N : ℝ) : ℂ)) := by
  rw [jetComplexCoordinates_apply]
  have h (q : ℂ) (t : ℝ) :
      ((q.re / t : ℝ) : ℂ) + ((q.im / t : ℝ) : ℂ) * Complex.I = q / (t : ℂ) := by
    simp only [Complex.ofReal_div]
    rw [div_mul_eq_mul_div, ← add_div, Complex.re_add_im]
  exact Prod.ext (h _ _) (h _ _)

/-- Polynomial evaluation and radial derivative thresholds are exactly the closed jet event. -/
theorem mem_jetSmallBallSet_rademacher (N : ℕ) (hN : 0 < N) (r : ℝ) (z : ℂ)
    (ω : LogMoments.SignVector N) (u v : ℝ) :
    realRademacherJet N r z ω ∈ jetSmallBallSet u v ↔
      ‖(rademacherPolynomial N ω).eval (r * z)‖ ≤ u * Real.sqrt N ∧
      ‖(r * z) * (rademacherPolynomial N ω).derivative.eval (r * z)‖ ≤
        v * ((N : ℝ) * Real.sqrt N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  rw [realRademacherJet_eq_normalizedPolynomialJet]
  simp only [jetSmallBallSet, Set.mem_preimage, jetComplexCoordinates_normalizedPolynomialJet,
    Set.mem_prod, Metric.mem_closedBall, dist_zero_right, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos (mul_pos hn hs),
    div_le_iff₀ hs, div_le_iff₀ (mul_pos hn hs)]

/-- The joint value and derivative small-ball bound for the actual sign polynomial. -/
theorem exists_annular_polynomial_small_ball_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : 0 < N) (K r θ : ℝ)
      (_ : 0 ≤ K) (_ : 2 * K ≤ N)
      (_ : 1 - K / N ≤ r) (_ : r ≤ 1 + K / N)
      (_ : (6400 * Real.exp (8 * K)) ^ 2 ≤ (N : ℝ))
      (_ : 1 / Real.sqrt N ≤ ‖((2 * θ : ℝ) : Real.Angle)‖)
      (u v : ℝ) (_ : 0 ≤ u) (_ : 0 ≤ v),
      (LogMoments.signMeasure N).real {ω |
        ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤ u * Real.sqrt N ∧
        ‖(r * Complex.exp (Complex.I * θ)) *
          (rademacherPolynomial N ω).derivative.eval (r * Complex.exp (Complex.I * θ))‖ ≤
          v * ((N : ℝ) * Real.sqrt N)} ≤
        u ^ 2 * v ^ 2 / (4 * (Real.exp (-4 * K) / 80) ^ 2) +
          jetGaussianErrorConstant C K / Real.sqrt N := by
  obtain ⟨C, hC, hbound⟩ := exists_annular_jet_small_ball_constant
  refine ⟨C, hC, ?_⟩
  intro N hN K r θ hK hNK hrl hru hdegree hangle u v hu hv
  have h := hbound N hN K r θ hK hNK hrl hru hdegree hangle u v hu hv
  rw [measureReal_def, Measure.map_apply (measurable_of_finite _) (measurableSet_jetSmallBallSet u v)] at h
  have hevent : (realRademacherJet N r (Complex.exp (Complex.I * θ))) ⁻¹' jetSmallBallSet u v =
      {ω | ‖(rademacherPolynomial N ω).eval (r * Complex.exp (Complex.I * θ))‖ ≤ u * Real.sqrt N ∧
        ‖(r * Complex.exp (Complex.I * θ)) *
          (rademacherPolynomial N ω).derivative.eval (r * Complex.exp (Complex.I * θ))‖ ≤
          v * ((N : ℝ) * Real.sqrt N)} := by
    ext ω
    exact mem_jetSmallBallSet_rademacher N hN r (Complex.exp (Complex.I * θ)) ω u v
  rw [hevent] at h
  exact h

end Erdos522

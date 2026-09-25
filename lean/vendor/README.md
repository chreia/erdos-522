# Vendored libraries

This directory contains two Lean libraries by other authors. Each is licensed under the Apache License 2.0, and each keeps its license file and the copyright notice of every source file.

| Directory | Library | Authors | Upstream revision |
|---|---|---|---|
| [`ProbabilityApproximation`](ProbabilityApproximation) | [ProbabilityApproximation](https://github.com/Polarnova/ProbabilityApproximation), Berry–Esseen bounds and Bentkus's multivariate normal approximation | Asher Yan | release v0.9.6, [`c89fba9`](https://github.com/Polarnova/ProbabilityApproximation/tree/c89fba908a33ba741836407f43c67609e2d05279) |
| [`SLT`](SLT) | [Statistical Learning Theory in Lean 4](https://github.com/YuanheZ/lean-stat-learning-theory), including the Hanson–Wright inequality | Yuanhe Zhang, Jason D. Lee, Fanghui Liu and contributors | [`482a1a5`](https://github.com/YuanheZ/lean-stat-learning-theory/tree/482a1a56daf792b33afe8cf7f07f127dc0af8640) |

The upstream releases target Lean 4.32. The copies here are ported to Lean 4.34 and the Mathlib revision of this formalization. Where Mathlib 4.34 changed the meaning of a notion, as it did for the `eLpNorm` of a function that is not almost everywhere strongly measurable, the affected statements are restated so that they keep their original mathematical content, and a few compatibility lemmas are added. The production modules are included in full, and the upstream documentation, publishing and continuous-integration files are omitted. The local package version of ProbabilityApproximation is 0.9.7.

These are local ports for this formalization, not releases by the upstream authors.

## Modified files

Sebastien Kawada modified the files below in 2026 to port them to Lean v4.34.0 and Mathlib `5ed2965`. Each modified Lean file, and each configuration file that allows comments, carries a notice after its original header. All other files are identical to the upstream revisions above.

<details><summary><code>ProbabilityApproximation</code>: 48 files</summary>

- `.gitignore`
- `ProbabilityApproximation/Bentkus/CutoffDerivativeGaussianIBP.lean`
- `ProbabilityApproximation/Bentkus/GaussianCompanionMoments.lean`
- `ProbabilityApproximation/Bentkus/GaussianDensityDerivatives.lean`
- `ProbabilityApproximation/Bentkus/Induction.lean`
- `ProbabilityApproximation/Bentkus/Induction/GaussianDensityComparison.lean`
- `ProbabilityApproximation/Bentkus/Induction/IdentityCovarianceReduction.lean`
- `ProbabilityApproximation/Bentkus/Induction/LargeAngleEstimate.lean`
- `ProbabilityApproximation/Bentkus/Induction/SmallAngleEstimate.lean`
- `ProbabilityApproximation/Bentkus/Induction/SplitGaussianShell.lean`
- `ProbabilityApproximation/Bentkus/InductionBranches.lean`
- `ProbabilityApproximation/Bentkus/ProbabilitySpaceTransport.lean`
- `ProbabilityApproximation/Bentkus/Rotation.lean`
- `ProbabilityApproximation/Bentkus/RotationIntegration.lean`
- `ProbabilityApproximation/Bentkus/SmoothingInequality.lean`
- `ProbabilityApproximation/Bentkus/Whitening.lean`
- `ProbabilityApproximation/ChenShao/CDFReflection.lean`
- `ProbabilityApproximation/ChenShao/Concentration.lean`
- `ProbabilityApproximation/ChenShao/ExponentialConcentration.lean`
- `ProbabilityApproximation/ChenShao/Leaves.lean`
- `ProbabilityApproximation/ChenShao/NonuniformAssembly.lean`
- `ProbabilityApproximation/ChenShao/NonuniformLargeGamma.lean`
- `ProbabilityApproximation/ChenShao/NonuniformStein.lean`
- `ProbabilityApproximation/ChenShao/TruncationComparison.lean`
- `ProbabilityApproximation/ChenShao/UniformBerryEsseen.lean`
- `ProbabilityApproximation/ChenShao/UpperTruncatedIndicator.lean`
- `ProbabilityApproximation/ChenShao/UpperTruncatedResidual.lean`
- `ProbabilityApproximation/ChenShao/UpperTruncatedSteinBounds.lean`
- `ProbabilityApproximation/ChenShao/UpperTruncation.lean`
- `ProbabilityApproximation/ConvexGeometry/BallCauchyProjection.lean`
- `ProbabilityApproximation/ConvexGeometry/BallGaussianPerimeter.lean`
- `ProbabilityApproximation/ConvexGeometry/BallProjectionArea.lean`
- `ProbabilityApproximation/ConvexGeometry/BallRadialMass.lean`
- `ProbabilityApproximation/ConvexGeometry/BallSphereHausdorff.lean`
- `ProbabilityApproximation/ConvexGeometry/BallSphereMeasure.lean`
- `ProbabilityApproximation/ConvexGeometry/BallSphereMoments.lean`
- `ProbabilityApproximation/ConvexGeometry/BallSphericalProjection.lean`
- `ProbabilityApproximation/ConvexGeometry/GaussianShell.lean`
- `ProbabilityApproximation/ConvexGeometry/GaussianShellCoarea.lean`
- `ProbabilityApproximation/ConvexGeometry/MetricProjection.lean`
- `ProbabilityApproximation/ConvexGeometry/ParallelSets.lean`
- `ProbabilityApproximation/ConvexGeometry/ScalarCoarea.lean`
- `ProbabilityApproximation/ConvexGeometry/SmoothCutoff.lean`
- `ProbabilityApproximation/ConvexGeometry/SquaredDistance.lean`
- `ProbabilityApproximation/ConvexGeometry/SupportingNormal.lean`
- `lake-manifest.json`
- `lakefile.toml`
- `lean-toolchain`

</details>

<details><summary><code>SLT</code>: 45 files</summary>

- `SLT/ConvergenceL1Subseq.lean`
- `SLT/CoveringNumber.lean`
- `SLT/Dudley.lean`
- `SLT/EfronStein.lean`
- `SLT/GaussianLSI/BernoulliLSI.lean`
- `SLT/GaussianLSI/DualEntApp.lean`
- `SLT/GaussianLSI/DualityEntropy.lean`
- `SLT/GaussianLSI/OneDimGLSI.lean`
- `SLT/GaussianLSI/SubAddEnt/Subadditivity.lean`
- `SLT/GaussianLSI/TensorizedGLSI.lean`
- `SLT/GaussianLipConcen.lean`
- `SLT/GaussianMeasure.lean`
- `SLT/GaussianPoincare/EfronSteinApp.lean`
- `SLT/GaussianPoincare/LevyContinuity.lean`
- `SLT/GaussianPoincare/Limit.lean`
- `SLT/GaussianSobolevDense/Cutoff.lean`
- `SLT/GaussianSobolevDense/Defs.lean`
- `SLT/GaussianSobolevDense/Density.lean`
- `SLT/GaussianSobolevDense/Mollification.lean`
- `SLT/HansonWright.lean`
- `SLT/LeastSquares/DudleyApplication.lean`
- `SLT/LeastSquares/L1Regression/L1CoveringBound.lean`
- `SLT/LeastSquares/LinearRegression/EntropyIntegral.lean`
- `SLT/LeastSquares/LinearRegression/EuclideanReduction.lean`
- `SLT/LeastSquares/LinearRegression/LocalizedBall.lean`
- `SLT/LeastSquares/LinearRegression/MinimaxRate.lean`
- `SLT/LeastSquares/Localization.lean`
- `SLT/LeastSquares/MasterErrorBound.lean`
- `SLT/LeastSquares/SubGaussianity.lean`
- `SLT/LipschitzProperty.lean`
- `SLT/MatrixInfra/Basic.lean`
- `SLT/MatrixInfra/CourantFischer.lean`
- `SLT/MatrixInfra/EYM.lean`
- `SLT/MatrixInfra/MatCalc.lean`
- `SLT/MatrixInfra/Perturb.lean`
- `SLT/MeasureInfrastructure.lean`
- `SLT/RMT/Basic.lean`
- `SLT/RMT/MatBern.lean`
- `SLT/SeparableSpaceSup.lean`
- `SLT/SmallBallProb.lean`
- `SLT/SubGaussian.lean`
- `SLT/TDudley.lean`
- `lake-manifest.json`
- `lakefile.lean`
- `lean-toolchain`

</details>

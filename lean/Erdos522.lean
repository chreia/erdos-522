/-
Copyright (c) 2026 Sebastien Kawada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastien Kawada
-/

import Erdos522.Probability.RademacherZeroDistribution
import Erdos522.Probability.RadialProfile
import Erdos522.Probability.LogMoments.UniformLogarithmicMoments
import Erdos522.Probability.IndependentCoefficientRadialLaws
import Erdos522.Probability.RademacherLogarithmicRootRate
import Erdos522.Probability.EventualLogarithmicRootRate
import Erdos522.Probability.RealPowerRadialInterpolation
import Erdos522.Probability.WeightedConstantTerm
import Erdos522.Probability.NearbyCircleSublevelCounts
import Erdos522.Analysis.KacRadialProfile

/-!
# Critical-scale radial laws for nested random polynomials

The main results are `Erdos522.erdos_522`,
`Erdos522.radial_profile_compact_uniform_prefixes`, and
`Erdos522.LogMoments.uniform_logarithmic_moments`.

The same radial law holds for Gaussian, Steinhaus, and nontrivial bounded centrally
symmetric coefficients. Further results give a logarithmic almost-sure rate,
also stated as an eventual bound,
admissible sparse degree schedules, power-weighted variance profiles, and
summable bounds for sublevel components meeting nearby circles.
-/

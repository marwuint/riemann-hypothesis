import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexPointsBase
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PProjPointContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PFractionContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PGermFraction
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PLocalLift
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PRegularContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace ComplexMetric

theorem ProjPointContinuous.full : ProjPointContinuous.Statement.{u} :=
  ProjPointContinuous.proof

theorem FractionContinuous.full : FractionContinuous.Statement.{u} :=
  FractionContinuous.proof

theorem GermFraction.full : GermFraction.Statement.{u} :=
  GermFraction.proof

theorem LocalLift.full : LocalLift.Statement.{u} :=
  LocalLift.proof

theorem RegularContinuous.full : RegularContinuous.Statement.{u} :=
  RegularContinuous.proof ProjPointContinuous.full FractionContinuous.full GermFraction.full
    LocalLift.full

end ComplexMetric

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

def standardMetricOf (X : ProjScheme A N) : X.ContinuousMetric (𝟙_ X.X.Modules) :=
  X.standardMetric ComplexMetric.RegularContinuous.full

def standardMetricSelf (A : Type u) [CommRing A] (N : ℕ) :
    (ProjScheme.self A N).ContinuousMetric (𝟙_ (ProjScheme.self A N).X.Modules) :=
  (ProjScheme.self A N).standardMetricOf

end ProjScheme

end

end GroundTheory.Heights₂.Heights

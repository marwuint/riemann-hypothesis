import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem inputs_holds : Inputs :=
  ⟨Formalism.L2.SG.BesselDiscreteSeries.decLow, Coef.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end

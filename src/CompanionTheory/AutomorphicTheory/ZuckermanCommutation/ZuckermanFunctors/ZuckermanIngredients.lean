import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTraceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategoryStatement
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2Statement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIsoStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegralityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLawsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplexStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps where
  infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  decOfInj := decomposition_of_injective
  decOfTrace := GlobalTheory.T.DecompositionOfTrace
  homCat := GlobalTheory.T.HomCategory
  okTriv := trivial_rep_admissible
  okVr := vector_rep_admissible
  okWedge := _root_.GlobalTheory.CompanionTheory.ZuckWedge.okWedge
  okTens := _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
  matHom := _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom
  uIso := GlobalTheory.T.UnitaryIso
  homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
  casSplit := GlobalTheory.T.CasimirSplitting
  casDS := GlobalTheory.T.CasimirDiagonalSum
  wedgeInt := GlobalTheory.T.ExteriorIntegrality
  wedgeQ := _root_.GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD _root_.GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
  schur := CompanionTheory.D.gk.FinalFormK.schur'
  adj := adj_of GlobalTheory.T.HomCategory _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom GlobalTheory.T.tensHom'
  multOne := multOne_of GlobalTheory.T.HomCategory _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD
    CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
  inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
  occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
  zuckH := GlobalTheory.T.zuckerman_hypothesis
  decTens := GlobalTheory.T.decomposition_of_tensor_from_hom_laws GlobalTheory.T.HomCategory _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
  toRaw := GlobalTheory.T.ToRawComplex
  count := _root_.GlobalTheory.CompanionTheory.ZuckCount.count

end CompanionTheory.Zuck

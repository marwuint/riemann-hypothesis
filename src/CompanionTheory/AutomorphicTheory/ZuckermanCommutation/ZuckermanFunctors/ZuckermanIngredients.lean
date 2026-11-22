import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps where
  infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  decOfInj := decomposition_of_injective
  decOfTrace := _root_.GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace
  homCat := _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat
  okTriv := trivial_rep_admissible
  okVr := vector_rep_admissible
  okWedge := _root_.GlobalTheory.CompanionTheory.ZuckWedge.okWedge
  okTens := _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
  matHom := _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom
  uIso := _root_.GlobalTheory.CompanionTheory.ZuckUIso.uIso
  homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
  casSplit := _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit
  casDS := _root_.GlobalTheory.CompanionTheory.CasimirDS.casDS
  wedgeInt := _root_.GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
  wedgeQ := _root_.GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD _root_.GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
  schur := CompanionTheory.D.gk.FinalFormK.schur'
  adj := adj_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom
  multOne := multOne_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD
    CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
  inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
  occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
  zuckH := _root_.GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds
  decTens := _root_.GlobalTheory.CompanionTheory.ZuckDecTens.decTens _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
  toRaw := _root_.GlobalTheory.CompanionTheory.ZuckToRaw.toRaw
  count := _root_.GlobalTheory.CompanionTheory.ZuckCount.count

end CompanionTheory.Zuck

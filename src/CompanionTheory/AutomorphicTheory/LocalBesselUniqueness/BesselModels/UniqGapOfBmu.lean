import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WuFinal
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AmplitudeOrbitalIntegral
import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.HasDerivAtMatrixExpZero
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.AutomorphicTheory.RankOneTori.KDense

namespace CompanionTheory.Lime.BM

theorem wuDecayOfGap (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap h

theorem ampUnif (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.L2.S.Pv.AmpOrbCoef.BM.ampUnif_gap h
    fun k r ε lam H _ _ _ σ hl hσ v hv Ws hWs e he => Formalism.MainStatements.RankOne.KD.kDense k r ε lam H σ hl hσ v hv Ws hWs e he

end CompanionTheory.Lime.BM

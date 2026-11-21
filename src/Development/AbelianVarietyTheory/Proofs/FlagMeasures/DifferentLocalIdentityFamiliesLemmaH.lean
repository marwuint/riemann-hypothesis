import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HtDelta
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower

namespace GlobalTheory.HTieLeaf

theorem main : Formalism.L2.SG.FamDefs.HTie :=
  Formalism.L2.SG.NGHTie.hTie_of _root_.GlobalTheory.HTPlaceLeaf.htPlace GlobalTheory.DiffModProd.htDelta _root_.GlobalTheory.HTThetaLeaf.main

end GlobalTheory.HTieLeaf

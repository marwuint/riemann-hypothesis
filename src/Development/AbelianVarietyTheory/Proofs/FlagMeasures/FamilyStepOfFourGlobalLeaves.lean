import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie

namespace GlobalTheory

theorem stepFamC_of_globalLeaves :
    Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric →
      Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC :=
  fun hG5 hW hG4 hE =>
    Formalism.L2.SG.FamDefs.stepFamC_of (fun D h => _root_.GlobalTheory.localMass_le_genericMass_nine _ _ h) _root_.GlobalTheory.HTieLeaf.main hG5 hW hG4 hE

end GlobalTheory

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPair
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsotropicOrthHyp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact _root_.GlobalTheory.HypPrimVec.exists_primitive_norm_neg
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat

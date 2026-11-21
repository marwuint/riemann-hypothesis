import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton

noncomputable section

namespace GlobalTheory.HCFinU

open NumberField Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bridgeS (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    I.GA ≃ₜ* GlobalTheory.AdelicU.GAd s I.J := by
  subst hs
  exact Formalism.L2.SG.AdBridge.toHA I (Formalism.L2.SG.Closed.AdBridgeIso_holds I)

end GlobalTheory.HCFinU

end

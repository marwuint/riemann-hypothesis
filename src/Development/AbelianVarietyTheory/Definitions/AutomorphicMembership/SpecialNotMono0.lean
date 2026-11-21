import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.L2.Host GlobalTheory.WeilDeligne

theorem setBC_self (D : D7) : setBC D D.nbc = D := rfl

theorem setTy_self (D : D7) (hE : IsEmpty D.nd.Loc) : setTy D hE D.ntypes D.nStage_trivialCharacter_compat D.nStage_trivialCharacter_coeff_eq = D := rfl

theorem setCG_CG (D : D7) (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) : (setCG D hE K).naut.CG = K.CG := rfl

end GlobalTheory.HeightCounting

end

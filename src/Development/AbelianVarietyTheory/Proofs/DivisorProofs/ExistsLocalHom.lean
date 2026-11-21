import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary

noncomputable section

namespace GlobalTheory.ThK.LocalHom

end GlobalTheory.ThK.LocalHom

section LocalHomAux2

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ThK.LocalHom

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

section Grp

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem mat_mul {J : Matrix (Fin n) (Fin n) E} (a b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (a * b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat a * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat b := rfl

theorem mat_one {J : Matrix (Fin n) (Fin n) E} : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) = 1 := rfl

end Grp

end GlobalTheory.ThK.LocalHom

end LocalHomAux2

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

end

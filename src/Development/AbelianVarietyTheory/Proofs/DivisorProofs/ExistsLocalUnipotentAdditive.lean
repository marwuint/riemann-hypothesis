import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_algebraMap (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (u : AF F) :
    compFin F E v (algebraMap (AF F) (AE F E) u) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (evFin F v u) := rfl

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
end GlobalTheory.LinBarCoords

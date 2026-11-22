import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.MiTop

theorem fixAux {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (hId : GlobalTheory.Core.Mi.IdE X) (S : Set (Fin X.B.I.n → X.B.I.E)) (p : Fin X.B.I.n → X.B.I.E) (hp : p ∈ S)
    (g : GA D (D.sp.Y 0))
    (hg : (iotaX X h g).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS X.B.I S ∧ (iotaX X h g).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS X.B.I S) :
    Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) g) (fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k)))) =
      fun k => Formalism.L2.Theta.incA D (X.ιE (p (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) := by
  have hR := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hId h (GlobalTheory.Core.Mi.rank_eq X h) S
    (Formalism.IndefR.RationalEmbedding.iota D g)).1 hg
  exact (GlobalTheory.Core.SBesLevi.bridge_fix D g _).2 (hR p hp)

end GlobalTheory.MiTop

end

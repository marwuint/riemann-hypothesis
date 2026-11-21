import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open Formalism.L2.SG.PoincareInHH Formalism.L2.SG.PoincareInHH.PoincareSetting
open Formalism.L2.SG.HidaSetting (HidaSetting rv incl)
open Formalism.L2.SG.InstExistsPf (instOf)
open Formalism.L2.SG.RowsJoinPinned (iotaX castGA)
open Formalism.MainNotions.S (AutInst uMat)
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

variable {D : D7}

def castV {I I' : AutInst} (h : I = I') (x : Fin I.n → I.E) : Fin I'.n → I'.E := h ▸ x

def crdY {I : AutInst} (h : I = instOf D) (x : Fin I.n → I.E) : Fin (D.sp.Y 0).rank → D.host.E := castV h x

section Frame

variable (X : HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word) {V₀ A L : HSp D}
  (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)

structure IsFrame : Prop where
  e_eq : ∀ a i, d.e i a = crdY h (X.eR a) i
  f_eq : ∀ a i, d.e' i a = crdY h (X.fR a) i
  line : IsLineVec L ζ
  z_eq : d.i₀ *ᵥ vecB o ζ = crdY h (X.zR u)

variable {X h u d o ζ}

end Frame

def thetaS (D : D7) : D.host.E := 1 / ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding

end

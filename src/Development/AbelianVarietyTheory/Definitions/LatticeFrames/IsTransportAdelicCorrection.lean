import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

variable {D : D7} {u : D.what₂.Word}

def chart0 (F : Formalism.L2.Forms.Forms0 D u) : GlobalTheory.AdForm.Chart D u 0 (Nat.zero_le _) where
  cl := (D.mem u).C.cls 0
  inc := id
  K := F.cls0.toChart
  eY := F.val0.eY

def IsTransportAdelicCorrection {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) (a : GA D (D.sp.X 0)) : Prop :=
  a ∈ GfC (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = tr.h0.1.1

def IsTypePlaces (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      ∃! PP, PP ∈ Pg ∧ PP.under (𝓞 D.host.F) = v

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

end GlobalTheory.Core.Mi

end

import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2

namespace SelJ

variable {D : D7} {X : Col.Fields}

def oEq (s : Ker.Seam D X) : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

def Carried (s : Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  P'.asIdeal = P.asIdeal.map (oEq s)

end SelJ

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def SelIn (R : RecT ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side

def SelSidePq (R : RecT ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ SelIn R (Set.range Pq)

end

end Formalism.L2

import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def SpanP : Prop :=
  ∀ i, ∀ S ∈ R.Wall i (sg0 D A), (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, S (fun ρ => v ρ) = 0) → S = 0

end Formalism.IndefR.Eqv.Act

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H),
    R.HE.e x ∈ R.EEat (R.levR F b) ↔
      ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

end GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Represents (R : RealDat D A Ks) (t : T) (y : (R.HX t).H →ₗ[ℂ] R.HE.H) : Prop :=
  ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))

end

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Represents.unique {R : RealDat D A Ks} (hE : R.models_HE) {t : T} {y y' : (R.HX t).H →ₗ[ℂ] R.HE.H}
    (h : Represents R t y) (h' : Represents R t y') : y = y' :=
  LinearMap.ext fun x => hE.1 ((h x).trans (h' x).symm)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence

end

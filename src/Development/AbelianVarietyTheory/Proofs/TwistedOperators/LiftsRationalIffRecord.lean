import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare

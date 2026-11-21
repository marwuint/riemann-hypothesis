import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (Φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g Φ

def IsThetaMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t) (kernelP R i t) (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
      ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
          thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

end

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

end

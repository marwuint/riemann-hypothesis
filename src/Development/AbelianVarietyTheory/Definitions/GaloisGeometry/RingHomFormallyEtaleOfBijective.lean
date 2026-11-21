import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open TopologicalSpace
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

section Etale

variable {X Y : Scheme.{0}}

def EtaleAtPt (f : X ⟶ Y) (x : X) : Prop := (f.stalkMap x).hom.FormallyEtale

end Etale

section Strata

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

def nonEtaleLocus (j : Fin n) : Set (C.B j.castSucc).left :=
  {x | ¬ EtaleAtPt (C.φ j).left x}

def stratSet (j : Fin n) : Set S :=
  closure ((C.B j.castSucc).hom.base '' nonEtaleLocus C j)

theorem isClosed_stratSet (j : Fin n) : IsClosed (stratSet C j) := isClosed_closure

def stratClosed (j : Fin n) : Closeds S := ⟨stratSet C j, isClosed_stratSet C j⟩

def stratIdeal (j : Fin n) : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (stratClosed C j)

@[simp] theorem coe_support_stratIdeal (j : Fin n) : ((stratIdeal C j).support : Set S) = stratSet C j :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

end Strata

end GlobalTheory.IwLevel

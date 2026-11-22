import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def QuotShape {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type}
    [AddCommGroup X] [Module O X] (Hc F : Submodule O X) (deg : ℕ) : Prop :=
  ∃ (Cy : Type) (_ : AddCommGroup Cy) (_ : Module O Cy)
    (ι : (Fin deg → KO O) →ₗ[O] (Hc ⧸ F.comap Hc.subtype))
    (π : (Hc ⧸ F.comap Hc.subtype) →ₗ[O] Cy),
    Function.Injective ι ∧ Function.Exact ι π ∧ ∃ c0 : Cy, ∀ y : Cy, ∃ a : O, y = a • c0

structure HZeroRowPlaceData (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (d : Type) (Mrow : Type) [AddCommGroup Mrow] [Module O Mrow] where

  D : InvariantsCohomologyData ℓ

  N : Submodule O (d → KO O)
  idn : D.M ≃+ N

  Cs : Type
  [gCs : AddCommGroup Cs]
  [mCs : Module O Cs]
  con : N →ₗ[O] Cs
  inc : Mrow →ₗ[O] Cs

attribute [instance] HZeroRowPlaceData.gCs HZeroRowPlaceData.mCs

def StatBKbConv : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A HV HT' HV' : Type) [AddCommGroup A] [Module O A]
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV'),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    (HfV.restrictScalars O).map q = annih pr ((HfV'.restrictScalars O).comap j')

def StatRowBK : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (X : Type) [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    (HV Cs HV' : Type)
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs] [Module.Finite O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) →
    F = ((HfV.restrictScalars O).map q).map Hc.subtype → Fs = (HfV'.restrictScalars O).comap j' →
    F = (annih pr Fs).map Hc.subtype

end Formalism.RepresentationBoundsCohomology.JT

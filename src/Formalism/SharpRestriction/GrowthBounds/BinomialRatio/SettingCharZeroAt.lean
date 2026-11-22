import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model Formalism.L2.G.Model.TS

def SettingCharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → CharZero Kf ∧ ¬ IsUnit ((p : ℕ) : O)

end Formalism.MainNotions.ColumnSystems.Pf

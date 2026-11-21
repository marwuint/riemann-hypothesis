import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def gen (Qq : Type) [Field Qq] (p : ℕ) (a : ℤ) : Fin 1 → Qq := fun _ => (p : Qq) ^ a

end Formalism.MainNotions.G.Inhab

end

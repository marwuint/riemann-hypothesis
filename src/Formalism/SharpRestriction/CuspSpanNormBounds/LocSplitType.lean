import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

def LocUnimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (L M : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E L → Submodule.IsLattice E M →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt S.hT p L → IsUnimodularAt S.hT p M →
      ∃ g ∈ isom S.hT, gmap g (loc (K := E) p L) = loc (K := E) p M

end Formalism.MainNotions.BridgeRowsGenus

end

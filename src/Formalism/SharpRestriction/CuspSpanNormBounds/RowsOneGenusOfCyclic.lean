import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Cyc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem cyc_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

end Cyc

end Formalism.MainNotions.BridgeRowsGenus

end

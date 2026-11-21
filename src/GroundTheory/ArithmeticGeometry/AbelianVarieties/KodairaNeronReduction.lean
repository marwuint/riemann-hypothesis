import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  {π : 𝒪} (hπ : Irreducible π)

local notation "ι" => algebraMap 𝒪 K

instance isIntegral_map : IsIntegral 𝒪 (W.map (algebraMap 𝒪 K)) := ⟨⟨W, rfl⟩⟩

include hπ

end Reduction

end

end GroundTheory.Arith.Abelian

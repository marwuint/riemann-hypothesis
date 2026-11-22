import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
import GroundTheory.GlobalFields.NormResidueSymbol.Rational
import GroundTheory.GlobalFields.NormResidueSymbol.Surjective

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

end CyclotomicSymbol

end

end GroundTheory.Global

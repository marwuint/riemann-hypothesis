import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationUniqueUpToConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

section Loc

variable (D : D7) (i : D.nd.Loc)

theorem coe_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : (Units.coeHom _).comp (mapRep f ρ) = mapM f ((Units.coeHom _).comp ρ) := rfl

variable {D i}

end Loc

end GlobalTheory.ConstituentsCompare

end

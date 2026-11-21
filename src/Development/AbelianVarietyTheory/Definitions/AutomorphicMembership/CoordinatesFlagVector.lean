import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameRedEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle

noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

def latV (Λ : Submodule (𝓞 E) (Fin S.rank → E)) : Submodule (𝓞 E) S.V :=
  Λ.comap ((S.frame.equivFun.restrictScalars (𝓞 E) : S.V ≃ₗ[𝓞 E] (Fin S.rank → E)) : S.V →ₗ[𝓞 E] _)

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}

theorem mem_latV (x : S.V) : x ∈ latV S Λ ↔ co S x ∈ Λ := Iff.rfl

end GlobalTheory.IntPair

end

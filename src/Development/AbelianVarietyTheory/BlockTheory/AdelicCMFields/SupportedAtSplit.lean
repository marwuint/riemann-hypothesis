import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct

section Notions

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def evalAt (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (E) in

def loc (v : HeightOneSpectrum (𝓞 F)) : RA F E →ₐ[F] v.adicCompletion F ⊗[F] E :=
  Algebra.TensorProduct.map (evalAt v) (AlgHom.id F E)

variable (F) in

def ratM {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun e => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e

def IsUnitaryA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ x y : Fin n → RA F E, hermA c G (g.mulVec x) (g.mulVec y) = hermA c G x y

variable (E) in

def IsSplitPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ w w' : Ideal (𝓞 E), w ≠ w' ∧ w.IsPrime ∧ w'.IsPrime ∧
    w.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ w'.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal

end Notions

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation

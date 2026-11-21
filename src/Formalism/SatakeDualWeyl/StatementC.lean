import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG

section Defs

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))

def levelVL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] v.adicCompletion F)) :=
  level (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)

def levelAfL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  level (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)))
    (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)

def evalV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def prV [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* E ⊗[F] v.adicCompletion F :=
  (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v)).toRingHom

end Defs

def LevelAfLStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J

def ClassSetFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    Finite (ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))

def AdelicStabFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F),
      Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g)

def DefSig : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (n : Type) [Fintype n] [DecidableEq n]
    (σ : E →ₐ[F] E) (J : Matrix n n E) (ι : F →+* ℝ) (τ : E →+* ℂ),
    τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ →
    τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    IsHerm (σ : E →+* E) J → IsUnit J.det →
    (IsDefiniteAt σ J ι ↔
      (HasSignature (J.map τ) (Fintype.card n) 0 ∨ HasSignature (J.map τ) 0 (Fintype.card n)))

def StdFormDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) → NumberField.IsTotallyReal F →
    IsHerm (σ : E →+* E) (1 : Matrix n n E) ∧ IsTotDef σ (1 : Matrix n n E) ∧ IsTotDef σ (-1 : Matrix n n E)

end Formalism.UG

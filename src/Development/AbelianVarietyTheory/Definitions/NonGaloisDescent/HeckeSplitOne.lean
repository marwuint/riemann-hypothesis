import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace GlobalTheory.LiftLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LabCompat (i : N.Loc) : Prop := ∀ σ Sig, HasParamW N A i σ Sig → (N.goodRow σ ↔ goodSig N A Sig)

def AtMOfParam (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → ∀ σ, HasParamW N A i σ Sig → AtM N A i σ

def CharSum : Prop :=
  ∀ (w : PlE H) (a b χ : A.LP w) (s : ℝ), A.lpDim χ = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧ A.lpChar (A.lpZero w) χ = A.lpZero w

end Rec

section Exp

open Formalism.MainNotions.IntegralHeckeForms

def CommG (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (D.nexp.actG i j b g).toLinearMap ∘ₗ D.nexp.hkF i j b k P = D.nexp.hkF i j b k P ∘ₗ (D.nexp.actG i j b g).toLinearMap

end Exp

end GlobalTheory.LiftLeaf

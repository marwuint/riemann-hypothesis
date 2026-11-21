import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a

open Classical in

def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g

end GlobalTheory.K4

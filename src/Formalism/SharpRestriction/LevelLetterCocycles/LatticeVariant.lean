import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def evA (i : X.Tw) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) : LamO X i Q M →ₐ[X.O i] X.Ok i k :=
  AddMonoidAlgebra.lift (X.O i) (X.Ok i k) (DelQM D.host (X.l i) Q M) ((Units.coeHom (X.Ok i k)).comp χ)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

structure RFam (i : X.Tw) where
  B : ∀ j b, Submodule (X.O i) (Y.Fm i j b)
  A : ∀ j b, Module.End (X.O i) (Y.Fm i j b)
  Sg : ∀ j b, Set (Y.Dat i j b)
  S : ∀ j b, Finset (Y.Dat i j b)
  kap : ∀ j b, Module.End (X.O i) (Y.Fm i j b)

variable {Y}

def RFam.Th {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) : Submodule (X.O i) (Y.Fm i j b) :=
  (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b (F.Sg j b)).map (F.A j b)

variable (Y)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

end Formalism.MainNotions.LatticeVariant

end

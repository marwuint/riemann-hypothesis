import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

end Formalism.MainNotions.N.KillingConditions

end

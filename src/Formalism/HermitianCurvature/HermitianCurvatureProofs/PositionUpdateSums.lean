import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute

namespace Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Slot

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem finset_fin_two_eq_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  exact h i

def flipA (a : S) (u : Ix S) : Ix S := Function.update u a (Fin.rev (u a))

theorem flipA_invol (a : S) : Function.Involutive (flipA a) := by
  intro u
  funext b
  by_cases hb : b = a
  · subst hb; simp [flipA]
  · simp [flipA, Function.update_of_ne hb]

theorem sum_position {M : Type} [AddCommMonoid M] (a : S) (F : Ix S → M) :
    ∑ u, F u = ∑ u, if u a = 0 then F u + F (Function.update u a 1) else 0 := by
  have h1 : ∑ u, F u = ∑ u, ((if u a = 0 then F u else 0) + (if u a = 1 then F u else 0)) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rcases finset_fin_two_eq_cases (u a) with h | h <;> simp [h]
  have h2 : ∑ u, (if u a = 1 then F u else 0) =
      ∑ u, (if u a = 0 then F (Function.update u a 1) else 0) := by
    refine (Equiv.sum_comp (flipA_invol a).toPerm (fun u => if u a = 1 then F u else 0)).symm.trans ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Function.Involutive.coe_toPerm, flipA, Function.update_self]
    rcases finset_fin_two_eq_cases (u a) with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  rw [h1, Finset.sum_add_distrib, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

theorem free_zero {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (h : u a ≠ y a) :
    G u y = 0 := by
  have e := congrFun (congrFun (hG (u a) (u a)).eq u) y
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply] at e
  simp only [if_true, Function.update_eq_self] at e
  rw [e, if_neg (Ne.symm h)]

end Slot

section Vec

variable {A S V : Type} [Ring A] [Fintype S] [DecidableEq S] [AddCommGroup V] [Module A V]

end Vec

end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums

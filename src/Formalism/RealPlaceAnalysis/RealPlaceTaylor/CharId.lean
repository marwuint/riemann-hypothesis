import Formalism.RealPlaceAnalysis.StatementC
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds

open Finset Polynomial

noncomputable section

namespace Formalism.REAL

def CharId_M {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Fin n → V) where
  toFun y := fun a => ∑ b, E a b (y b)
  map_add' y z := by funext a; simp [Finset.sum_add_distrib]
  map_smul' c y := by funext a; simp [Finset.smul_sum]

theorem CharId_M_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (y : Fin n → V) (a : Fin n) :
    CharId_M E y a = ∑ b, E a b (y b) := rfl

def twistedAction {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) : Module.End ℂ (Fin n → V) where
  toFun y := fun x => E c d (y x) - if x = d then y c else 0
  map_add' y z := by
    funext x; by_cases h : x = d <;> simp [h] <;> abel
  map_smul' r y := by
    funext x; by_cases h : x = d <;> simp [h, smul_sub]

theorem CharId_T_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (y : Fin n → V) (x : Fin n) :
    twistedAction E c d y x = E c d (y x) - if x = d then y c else 0 := rfl

end Formalism.REAL

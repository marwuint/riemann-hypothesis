import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv

open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinRow

def posFn {m : ℕ} (j o : ℕ) : Fin m ⊕ Fin j → ℕ
  | .inl a => if (a : ℕ) < o then a else a + j
  | .inr w => o + w

theorem posFn_lt {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) : posFn j o x < N := by
  rcases x with a | w
  · have := a.2
    simp only [posFn]
    split_ifs <;> omega
  · have := w.2
    simp only [posFn]
    omega

theorem posFn_injective {m j o : ℕ} (ho : o ≤ m) :
    Function.Injective (posFn j o : Fin m ⊕ Fin j → ℕ) := by
  rintro (a | w) (b | w') hxy <;> simp only [posFn] at hxy
  · have : (a : ℕ) = b := by split_ifs at hxy <;> omega
    exact congrArg _ (Fin.ext this)
  · have := w'.2
    exfalso
    split_ifs at hxy <;> omega
  · have := w.2
    exfalso
    split_ifs at hxy <;> omega
  · exact congrArg _ (Fin.ext (by omega))

def eo {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) : Fin m ⊕ Fin j ≃ Fin N :=
  Equiv.ofBijective (fun x => ⟨posFn j o x, posFn_lt h ho x⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y hxy => posFn_injective ho (congrArg Fin.val hxy), ?_⟩
    simp [h])

theorem eo_val {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) :
    ((eo h ho x : Fin N) : ℕ) = posFn j o x := rfl

end GlobalTheory.CompanionTheory.TyFinRow

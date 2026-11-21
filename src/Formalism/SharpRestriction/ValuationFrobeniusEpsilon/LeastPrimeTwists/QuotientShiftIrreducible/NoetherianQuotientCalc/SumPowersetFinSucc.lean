import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

end Formalism.MainNotions.V.Pf.V2.Calc

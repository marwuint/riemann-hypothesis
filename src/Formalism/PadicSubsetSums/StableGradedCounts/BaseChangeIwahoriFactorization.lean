import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact
import Lemmata.FirstBlockLemmaG.Imports
import Lemmata.MiscLemmasA.Imports

namespace Formalism.IrreducibleCountingLemmas.Z

theorem isUnit_sub_of_mem_maximalIdeal {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  first | exact Bl.FirstBlockLemmaG.goal1 .. | (apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha hm | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O

theorem iwahori_factorization_exists (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := Bl.SecondBlockLemmaB.goal1 O U L hL

end Formalism.IrreducibleCountingLemmas.Z

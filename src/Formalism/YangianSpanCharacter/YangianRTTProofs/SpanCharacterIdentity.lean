import Mathlib

namespace Formalism.YangianSpanCharacter.P

open Finset

private lemma rep_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (f f' : Fin n → V) (hli : LinearIndependent K (Sum.elim f f')) (p q p' q' : Fin n → K)
    (h : ∑ i, (p i • f i + q i • f' i) = ∑ i, (p' i • f i + q' i • f' i)) :
    ∀ i, p i = p' i ∧ q i = q' i := by
  have key := (Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q')
    (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)
  exact fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩

end Formalism.YangianSpanCharacter.P

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Rep

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

def IsSemisimplificationOf {W V : Type} [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) : Prop :=
  IsSS s ∧ ∃ (m : ℕ) (Ws : Fin m → Submodule k W) (e : W ≃ₗ[k] V),
    (∀ j, Stable s (Ws j)) ∧ DirectSum.IsInternal Ws ∧
    ∀ j g, ∀ v ∈ Ws j, ρ g (e v) - e (s g v) ∈ (⨆ j' ∈ Set.Iio j, Ws j').map (e : W →ₗ[k] V)

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

abbrev RepFam : Type := D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))

end Loc

end GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents

end

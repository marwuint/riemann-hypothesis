import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

section Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
  (bkP : BlochKatoReduction.Gen.BKPh X) (E : IntegralHeckeForms.ExpDat Y)

def GoodAll (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (A Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, IsCoprime a (X.l i : ℤ) → IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

variable {Y bkP E}

end Gen

end GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

end

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end

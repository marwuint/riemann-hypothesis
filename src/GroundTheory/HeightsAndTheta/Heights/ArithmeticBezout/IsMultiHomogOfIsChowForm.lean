import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)

def blk (n : ℕ) : Fin n → (Σ _ : Unit, PBlk n ()) := fun i => ⟨(), i⟩

variable {n : ℕ}

theorem specFirst_eq {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by
  rw [specFirst, IndefiniteRowSideFullHecke.ArithBezout.specFirst, aeval_eq_bind₁]
  rfl

theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by
  have h : (fun ij => map φ (specFirstVar u ij)) =
      (specFirstVar (φ ∘ u) : Fin (e + 1) × Fin n → MvPolynomial (Fin e × Fin n) S) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [specFirstVar]
  rw [← specFirst_eq, ← specFirst_eq, specFirst, specFirst, map_bind₁, h]

end ObjectsChow

end GroundTheory.Heights₂.Heights

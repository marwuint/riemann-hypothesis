import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}

def finIdeal (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℤ) :=
  P.comap (rename fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))

def cycleChowForm {ι R σ : Type*} [CommSemiring R] (Z : ι →₀ ℕ) (f : ι → MvPolynomial σ R) :
    MvPolynomial σ R :=
  Z.prod fun W m => f W ^ m

def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1

end Objects

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end

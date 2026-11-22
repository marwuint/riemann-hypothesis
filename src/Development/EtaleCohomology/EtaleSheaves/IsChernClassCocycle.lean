import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.AlexanderWhitneyCupPullbackNaturality

def pcoc {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    Cocycle ((chains R).obj E) I n :=
  zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)

theorem cpull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (I : Cx R) {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    cpull ((chains R).map f) I n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

theorem pull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) {n : ℤ}
    (α : Cocycle ((chains R).obj E') (res R F) n) : pull R f F n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

end LateralTheory.E.AlexanderWhitneyCupPullbackNaturality

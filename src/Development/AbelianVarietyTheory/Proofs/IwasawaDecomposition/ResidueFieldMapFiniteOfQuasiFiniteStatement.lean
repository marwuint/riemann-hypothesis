import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFieldMap_finite_of_quasiFinite : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) [LocallyQuasiFinite g] (y : Y), (g.residueFieldMap y).hom.Finite := by
  exact @GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite

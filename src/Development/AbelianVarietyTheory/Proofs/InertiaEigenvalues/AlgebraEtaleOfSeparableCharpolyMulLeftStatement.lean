import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  exact @GlobalTheory.etale_of_separable_charpoly_mulLeft

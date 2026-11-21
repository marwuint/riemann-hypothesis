import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeight
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  exact @GlobalTheory.PlaceTop.thInt_of_oriented

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

namespace UpperTheory.affineWeylIwahoriData

section Tv
variable {k : Type} [Field k] {n : ℕ}

private def tv (a b : Fin n) (h : a ≠ b) (c : k) : GL (Fin n) k where
  val := transvection a b c
  inv := transvection a b (-c)
  val_inv := by rw [transvection_mul_transvection_same a b h]; simp
  inv_val := by rw [transvection_mul_transvection_same a b h]; simp

private theorem tv_val (a b : Fin n) (h : a ≠ b) (c : k) :
    (tv a b h c : Matrix (Fin n) (Fin n) k) = 1 + single a b c := rfl

end Tv

end UpperTheory.affineWeylIwahoriData


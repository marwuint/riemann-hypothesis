import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := GlobalTheory.EtC.hyp_spec_coAug_of_etFF

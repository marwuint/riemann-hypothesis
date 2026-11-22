import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwise
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := GlobalTheory.EtC.HCEqv.main

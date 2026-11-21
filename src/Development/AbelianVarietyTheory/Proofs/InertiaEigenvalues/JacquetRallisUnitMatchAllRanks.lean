import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  _root_.GlobalTheory.JR.unitMatch_of_weilField _root_.GlobalTheory.JR.WeilQuad.weilField_main

end GlobalTheory.JR

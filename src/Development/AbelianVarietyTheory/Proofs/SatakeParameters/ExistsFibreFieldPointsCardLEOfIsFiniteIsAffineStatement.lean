import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffine

open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine

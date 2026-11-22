import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kTriv_boxLB_powObj : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ),
    Out.KTriv (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) := by
  intro R _ P j
  have : IsCommMonObj P.A := P.isAb.comm
  exact _root_.GlobalTheory.kTriv_boxLB _ (Out.powObj P.A j) P.A j (Out.powIsPowGrp P.A j) P.L P.isLB P.ktriv

end GlobalTheory

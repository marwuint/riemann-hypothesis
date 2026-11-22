import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
@[reducible] def parametersOfDependence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL :=
  _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
end GlobalTheory.Mem.Top.Bl
end
end

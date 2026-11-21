import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic
open GroundTheory.Automorphic.Adele2
open Ad3 Ad3.R
open scoped NumberField.AdeleRing

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RankinSelberg

theorem weyl_inv_val {R : Type*} [CommRing R] :
    (((w0 : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] := rfl

end GlobalTheory.CompanionTheory.RankinSelberg

end

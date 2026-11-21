import Development.EtaleCohomology.DivisorCycles.OpenCoset
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPullOfPrincipalisation

namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => _root_.GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS (GlobalTheory.MixHt.arCalc_of_principalisation h) (_root_.GlobalTheory.HSNef.ampleHS_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory

import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffXMulPart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiltLePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NoethLocalHausdorff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemPowOfCoeffMem

noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

end GlobalTheory.PsCNL


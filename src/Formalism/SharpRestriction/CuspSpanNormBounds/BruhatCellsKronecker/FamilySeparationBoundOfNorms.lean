import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyExponentOfFormalDegree
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset
open scoped nonZeroDivisors NumberField

def SzfNormDD (D : D7) : Prop :=
  ((FractionalIdeal.absNorm (ddE D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2

theorem szf_card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (factCardPsi D.R D.host).1

end Formalism.MainNotions.BridgeLemma

end

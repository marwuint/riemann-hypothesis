import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
import Formalism.SharpRestriction.FamCore
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.RowsMemBaseField
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevM
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ NumberField Module

namespace FamInh

structure LvP where
  T : ℕ
  prime : T.Prime
  big : 991 < T
  π : 𝓞 H0.E
  mem : (π : H0.E) ∈ H0.K
  norm : (π : H0.E) * H0.conj (π : H0.E) = (T : H0.E)
  cong : (π - 1) ∈ Ideal.span {((H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2 : ℕ) : 𝓞 H0.E)}

instance (p : LvP) : Fact p.T.Prime := ⟨p.prime⟩

variable (p : LvP)

end FamInh

end GlobalTheory.Core.Rk

end

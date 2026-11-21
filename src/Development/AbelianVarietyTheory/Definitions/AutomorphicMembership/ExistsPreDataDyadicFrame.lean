import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

end GlobalTheory.Mem.PreXModel

end

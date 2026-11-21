import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.HostOrbitsPlaces
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.CoboundaryTransfers.Statement
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FrobeniusOrbits.Statement
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.StatementD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.RealPlaceAnalysis.StatementC

namespace Bl.general_b_fact_left_alt_form

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O]
    {W : Type} [inst_3 : AddCommGroup W] [inst_4 : Module (KK O) W] [inst_5 : Module O W]
    [inst_6 : IsScalarTower O (KK O) W] (M : Submodule O W) (y : W) :
    y ∈ MQ (K := KK O) M → ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  intro hy
  rw [Formalism.MainNotions.G.MQ] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨(s : O) * b, mul_ne_zero (nonZeroDivisors.ne_zero s.2) hb, ?_⟩
    have key : ((s : O) * b) • (c • x) = r • (b • x) := by
      rw [← algebraMap_smul (Formalism.MainNotions.G.KK O) ((s : O) * b) (c • x), smul_smul,
        ← algebraMap_smul (Formalism.MainNotions.G.KK O) r (b • x), ← algebraMap_smul (Formalism.MainNotions.G.KK O) b x, smul_smul]
      congr 1
      rw [map_mul, ← hrs]
      ring
    rw [key]
    exact M.smul_mem r hbx

end Bl.general_b_fact_left_alt_form

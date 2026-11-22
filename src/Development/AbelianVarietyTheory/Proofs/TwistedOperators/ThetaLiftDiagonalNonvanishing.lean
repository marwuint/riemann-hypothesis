import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpCuspApprox

theorem val_aut_cusp {D : D7} {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {F : N.Maps} (hF : F ∈ N.Cusp θ)
    (v : SmT N.M) : IsAutFunSm θ N.V (F v) ∧ IsCuspFun N.V (F v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 _).1 ((Formalism.IndefR.Mult.mem_multT θ N.M ∅ 1 F).1 hF)
  have e : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [e]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul c (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

end GlobalTheory.UpCuspApprox

namespace GlobalTheory.UpCuspApprox

end GlobalTheory.UpCuspApprox

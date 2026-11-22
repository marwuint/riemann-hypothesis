import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspLiftFiniteSumApproximation

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnCusp
variable {D : D7}

open GlobalTheory.Size in

theorem isCuspFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hU' : ∀ w, IsAutFun N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨(hx.aut w).toIsAutFun, hx.cusp w⟩
    | zero => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1 (hy w).1 (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_smul (hx w).1 c, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  suffices H : IsAutFun N.V ((PiTensorProduct.lift U) v) ∧ IsCuspFun N.V ((PiTensorProduct.lift U) v) from H.2
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.RowLift.isAutFun_smul (hU' f).1 r, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

end GlobalTheory.DnCusp

namespace GlobalTheory.DnCusp

end GlobalTheory.DnCusp

end

import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToTransposeGramGroupMapSurjective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefThetaNZ

section Darboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_zero {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (h : UA σ Wd.J) :
    M.I om 0 h = 0 := by
  simp [Model.I, theta, GlobalTheory.WeilM.thetaSum]

theorem I_smul' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ Wd.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    MeasureTheory.integral_const_mul]

theorem I_add' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd)
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} {h : UA σ Wd.J}
    (hΦ : MeasureTheory.IntegrableOn (fun g => theta om Φ g h) M.dom M.μ)
    (hΨ : MeasureTheory.IntegrableOn (fun g => theta om Ψ g h) M.dom M.μ)
    (hs : ∀ g, om (g, h) Φ ∈ GlobalTheory.WeilM.schA F _ ∧ om (g, h) Ψ ∈ GlobalTheory.WeilM.schA F _) :
    M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← MeasureTheory.integral_add hΦ hΨ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun g => ?_)
  show GlobalTheory.WeilM.thetaSum F (om (g, h) (Φ + Ψ)) = GlobalTheory.WeilM.thetaSum F (om (g, h) Φ) + GlobalTheory.WeilM.thetaSum F (om (g, h) Ψ)
  rw [map_add, GlobalTheory.WeilM.thetaSum_add F (hs g).1 (hs g).2]

end Darboux

end GlobalTheory.DefThetaNZ

namespace GlobalTheory.DefThetaNZ

end GlobalTheory.DefThetaNZ

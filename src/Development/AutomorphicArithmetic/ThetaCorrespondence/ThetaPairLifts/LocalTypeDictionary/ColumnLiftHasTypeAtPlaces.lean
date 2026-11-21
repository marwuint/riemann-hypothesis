import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelAdjointEqInvFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEachStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteUnitaryCuspidalDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmoothOfThetaLiftFiniteSum

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColTypeLift
theorem columnLift_isTypeAt_place : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ hI τ
  have h0 := xp_definite hG j hj.le
  have h1 := xp_definite hG (j + 1) hj
  obtain ⟨n, F, w, rfl⟩ := _root_.GlobalTheory.T.definite_unitary_cuspidal_decomposition hP R.θ (G.Xp j) hR.inf h0.1 h0.2 φ hφ
  obtain ⟨k, F', z, e⟩ := _root_.GlobalTheory.T.smooth_of_theta_lift_finite_sum hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ n F w hI
  rw [e]
  exact isTypeAt_sum R.θ (G.Xp (j + 1)) h1.1 h1.2 τ F' z
end GlobalTheory.ColTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place | exact _root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place | (intros; apply _root_.GlobalTheory.ColTypeLift.columnLift_isTypeAt_place <;> assumption)
end

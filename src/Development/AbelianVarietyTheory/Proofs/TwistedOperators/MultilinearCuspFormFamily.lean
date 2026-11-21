import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.GKGlobalise

theorem kFin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) = GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  apply le_antisymm
  · refine sSup_le fun W hW v hv => ?_
    exact ⟨W, hW.1, hv, hW.2⟩
  · rintro v ⟨A, hA, hv, hs⟩
    exact le_sSup (show A ∈ {W : Submodule ℂ (M.H τ) | FiniteDimensional ℂ W ∧
      Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W} from ⟨hA, hs⟩) hv

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun v hv =>
  (_root_.GlobalTheory.SmVecModel.mem_sm_iff M τ v).2 ((GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)).2.2.1 v hv)

end GlobalTheory.GKGlobalise

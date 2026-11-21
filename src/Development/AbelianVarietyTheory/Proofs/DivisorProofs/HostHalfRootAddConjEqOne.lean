import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFormReindex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.FrameEquiv.GenMove

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

variable {D : D7}

theorem isUnitFr_of_archM (W : HSp D) (X : Data D.host.E W.rank) (hX : ModelW W rfl X)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ} (h0 : IsOrthogonalFrame X x₀)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    (g : GA D W) (x : Frame X.Ψ W.rank)
    (hx : ∀ τ : X.Ψ, mat x τ = Matrix.reindex (finCongr rfl) (finCongr rfl) (archM W (th τ) g) * x₀ τ.1) :
    IsUnitFr X x := by
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x
    fun τ => ?_).2
  rw [← h0 τ.1 τ.2, hx τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary W (hth τ) g
  have e1 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) W.gram).transpose).map τ.1).transpose =
      -(W.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Adelic

end GlobalTheory.FrameEquiv.GenMove


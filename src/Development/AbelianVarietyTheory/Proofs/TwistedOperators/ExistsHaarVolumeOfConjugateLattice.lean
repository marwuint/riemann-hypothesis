import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellVolumeMulCoef

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellIdx

end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
end GlobalTheory.CellIdx

namespace GlobalTheory.CellIdx
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.RowRep GlobalTheory.SplitWeil

def suppGrp {D : D7} (e : AE D) (V : HSp D) : Subgroup (GA D V) where
  carrier := {g | SuppAt e V g}
  one_mem' := suppAt_iff.2 (by rw [GlobalTheory.MixModel.mt_one, sub_self, smul_zero])
  mul_mem' := GlobalTheory.LocGrp.suppAt_mul
  inv_mem' := fun {g} hg => suppAt_of_sandwich hg (-mt V g⁻¹) 1 (by
    rw [Matrix.mul_one, Matrix.neg_mul, Matrix.mul_sub, GlobalTheory.MixModel.mt_inv_mul, Matrix.mul_one, neg_sub])

instance {D : D7} (e : AE D) (V : HSp D) : (suppGrp e V).Normal :=
  ⟨fun g hg t => suppAt_of_sandwich hg (mt V t) (mt V t⁻¹) (by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.MixModel.mt_mul_inv])⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

set_option maxHeartbeats 1600000 in

theorem vol_mul_colCoef : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      la.real {n | (⟨b j, hb⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} *
        (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  first
  | (exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef)
  | exact @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef
  | (apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricJacobianSignature.cell_volume_mul_coef ..)

end GlobalTheory.CellIdx

end

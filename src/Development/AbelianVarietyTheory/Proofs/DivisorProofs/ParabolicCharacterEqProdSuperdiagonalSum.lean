import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

namespace GlobalTheory.PartsOccurProof

section Flip

variable {k k' : Type} [CommRing k] [CommRing k'] {r : ℕ}

def tw (x : GL (Fin r) k) : GL (Fin r) k where
  val := (x⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm
  inv := x.val.transpose.submatrix Fin.revPerm Fin.revPerm
  val_inv := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.submatrix_one_equiv]
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.submatrix_one_equiv]

theorem tw_apply (x : GL (Fin r) k) (i j : Fin r) : (tw x).val i j = (x⁻¹).val j.rev i.rev := rfl

end Flip

variable {D : D7}

end GlobalTheory.PartsOccurProof

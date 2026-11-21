import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfIsTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalComponentAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod Filter
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm hO_smul_left infPart_half)
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LocMod.Inhab

namespace GlobalTheory.LocMod.Exist

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)

def loc {m n : Type} (a : Matrix m n D.host.E) : Matrix m n k := a.map (p.π.comp (incA D))

theorem loc_gram_mul (V : HSp D) : loc p V.gram * loc p V.gram⁻¹ = 1 := by
  rw [loc, loc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne V).isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem loc_mul_gram (V : HSp D) : loc p V.gram⁻¹ * loc p V.gram = 1 := mul_eq_one_comm.1 (loc_gram_mul p V)

def dual (b : Matrix Y Y' k) : WO S T :=
  (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ.map fun z => cA D (p.ι z)

theorem up_mem (x : Matrix Y Y' k) : p.up FS FT x ∈ half S T p.e :=
  (isHalf_iff S T).1 fun _ _ => e_mul_ι p _

theorem dual_mem (b : Matrix Y Y' k) : dual p FS FT b ∈ half S T (cA D p.e) :=
  (isHalf_iff S T).1 fun _ _ => by
    simp only [dual, Matrix.map_apply]
    rw [← map_mul, e_mul_ι]

theorem up_add (x y : Matrix Y Y' k) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  ext i j
  simp only [Place.up, Matrix.mul_add, Matrix.add_mul, Matrix.map_apply, Matrix.add_apply, map_add]

theorem dual_add (x y : Matrix Y Y' k) : dual p FS FT (x + y) = dual p FS FT x + dual p FS FT y := by
  ext i j
  simp only [dual, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.map_apply, Matrix.add_apply, map_add]

theorem up_zero : p.up FS FT 0 = 0 := by simpa using up_add p FS FT 0 0

theorem dual_zero : dual p FS FT 0 = 0 := by simpa using dual_add p FS FT 0 0

theorem continuous_up : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem continuous_dual : Continuous (dual p FS FT) :=
  ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_transpose).matrix_map ((GlobalTheory.DualPairCompare.continuous_cA D).comp p.cont_ι)

theorem π_hO (x y : WO S T) : p.π (hO S T x y) = Matrix.trace
    (loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * Matrix.map x p.π) := by
  simp only [hO, map_sum, map_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, loc, Matrix.map_apply,
    Matrix.transpose_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem π_hO_dual (t b : Matrix Y Y' k) : p.π (hO S T (p.up FS FT t) (dual p FS FT b)) = ∑ r, ∑ q, b r q * t r q := by
  have h1 : (Matrix.map (dual p FS FT b) fun z => p.π (cA D z)) = (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ := by
    ext i j
    simp only [dual, Matrix.map_apply, cA_cA, p.π_ι]
  have h2 : Matrix.map (p.up FS FT t) p.π = FT.β * t * FS.γ := by
    ext i j
    simp only [Place.up, Matrix.map_apply, p.π_ι]
  rw [π_hO, h1, h2, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [loc_mul_gram, Matrix.one_mul, Matrix.mul_assoc _ _ (loc p T.gram), loc_mul_gram, Matrix.mul_one,
    Matrix.mul_assoc _ _ FT.β, FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [FS.γβ, Matrix.one_mul, Finset.sum_comm]
  rfl

theorem exists_dual {y : WO S T} (hy : IsHalf (cA D p.e) y) : ∃ b, dual p FS FT b = y := by
  refine ⟨(FS.γ * loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * FT.β)ᵀ, ?_⟩
  rw [dual, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ FS.β, FS.βγ, Matrix.mul_one, loc_gram_mul, Matrix.one_mul, Matrix.mul_assoc _ FT.β, FT.βγ,
    Matrix.mul_one, Matrix.mul_assoc, loc_gram_mul, Matrix.mul_one, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.map_apply, p.ι_π, map_mul, cA_cA]
  exact hy i j

theorem char_sympl {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (t b : Matrix Y Y' k) :
    ψ (symplO S T (p.up FS FT t) (dual p FS FT b)) = pairing ψk t b := by
  rw [pairing, ← π_hO_dual p FS FT, h, p.ι_π, ← hO_smul_left, (mem_half S T).1 (up_mem p FS FT t)]
  rfl

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

end GlobalTheory.LocMod.Exist
end

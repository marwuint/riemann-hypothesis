import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMtMulLeftAdelicMatrixHaarEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryAdelicMatrixAddHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem actO_map_haar : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (μ : Measure (WO S T)),
    μ.IsAddHaarMeasure → μ.map (actO S T g h) = μ := by
  intro D S T g h μ hμ
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hL : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) :=
    continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) :=
    continuous_id.matrix_mul continuous_const
  have e : actO S T g h =
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) ∘
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) := rfl
  rw [e, ← Measure.map_map hR.measurable hL.measurable, _root_.GlobalTheory.map_mt_mul_eq D T S.rank h μ hμ]
  exact _root_.GlobalTheory.AdelicModulus.map_mul_right_unitary D S T.rank g⁻¹ μ hμ

end GlobalTheory

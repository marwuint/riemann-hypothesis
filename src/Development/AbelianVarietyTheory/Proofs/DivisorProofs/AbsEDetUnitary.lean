import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParOpApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableRangeOneDetUnitElementary

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU
open GlobalTheory.WeilEx
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.WeilEx.Jac

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E))) = 1 := by
  set d := Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E)) with hd
  have hJu : IsUnit (incM F J).det := by
    have e0 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
    rw [e0]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have h := congrArg Matrix.det (show ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have h2 : (d : AE F E) * cA σ d = 1 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact hJu.mul_left_cancel (by linear_combination h)
  have hc : Units.map (cA σ : AE F E →* AE F E) d = conjUnit σ d := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rfl
  have h3 : d * Units.map (cA σ : AE F E →* AE F E) d = 1 := Units.ext (by simpa using h2)
  have h4 : absE F E d * absE F E d = 1 := by
    nth_rewrite 2 [← absE_conjUnit σ d]
    rw [← hc, ← map_mul, h3, map_one]
  apply NNReal.coe_injective
  have h6 : (absE F E d : ℝ) * absE F E d = 1 := by exact_mod_cast h4
  have h7 : (0 : ℝ) ≤ absE F E d := (absE F E d).2
  push_cast
  exact le_antisymm (by nlinarith) (by nlinarith)

end Main

end GlobalTheory.WeilEx.Jac

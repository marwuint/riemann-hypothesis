import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory
open Formalism.MainNotions.SumRepresentations.At

section Tw
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (g : Γ) :
    ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det • ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by
  simp only [twGL, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_map]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.GeneralLinearGroup.val_det_apply]

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have hu : ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (χ g).isUnit |>.ne_zero
    have := W.smul_mem (((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det)⁻¹ (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (h : IsSSRep ρ) :
    IsSSRep (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 hW', hc⟩

end Tw

theorem contQ_twGL (D : D7) (i : D.nd.Loc) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (hρ : ContQ D.nd i ρ) (hχ : ContQ D.nd i χ) :
    ContQ D.nd i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  unfold ContQ at *
  simp only [twGL_val]
  exact (hχ.matrix_det).smul hρ

end GlobalTheory

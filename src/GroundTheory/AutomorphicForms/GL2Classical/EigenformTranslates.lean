import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCosets
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCommute
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatake
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatakeRep
import GroundTheory.AutomorphicForms.GL2Classical.EigenQExpansion
import GroundTheory.AutomorphicForms.GL2Classical.CuspFormsFiniteDim
import GroundTheory.AutomorphicForms.GL2Classical.UnitaryEigenSpan
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace Manifold NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (k) in

def holoBddSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | MDiff F ∧ ∀ σ : SL(2, ℤ), IsBoundedAtImInfty (F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)}
  add_mem' {F G} hF hG := ⟨hF.1.add hG.1, fun σ => by
    rw [SlashAction.add_slash]
    exact (hF.2 σ).add (hG.2 σ)⟩
  zero_mem' := ⟨mdifferentiable_const, fun σ => by
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty⟩
  smul_mem' c F hF := ⟨hF.1.const_smul c, fun σ => by
    have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ σ).det.val := by
      rw [Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos
    rw [ModularForm.smul_slash, σ_of_det_pos hpos]
    exact (hF.2 σ).const_smul_left c⟩

theorem right_kGL_of_mem_translateSpan {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : ∀ g (w : ℂ) (hw : w ≠ 0), φ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * φ g)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan φ) :
    ∀ g (w : ℂ) (hw : w ≠ 0), ψ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * ψ g := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g w hw
    simp only [finRightRep_apply]
    rw [mul_assoc, realEmb_mul_finEmb_comm, ← mul_assoc, hφ]
  | zero => intro g w hw; simp
  | add x y _ _ hx hy => intro g w hw; simp [hx g w hw, hy g w hw, mul_add]
  | smul c x _ hx => intro g w hw; simp [hx g w hw]; ring

theorem posIdele_fst_rat (r : ℝ) (hr : 0 < r) :
    ((Reduction.posIdele (K := ℚ) r hr : Global.IdeleGroup ℚ) : 𝔸[ℚ]).1 =
      Global.RationalIdeles.realEquiv.symm r := by
  apply Global.RationalIdeles.realEquiv.injective
  rw [RingEquiv.apply_symm_apply, Global.RationalIdeles.realEquiv_apply]
  have := Reduction.infiniteProj_posIdele (K := ℚ) r hr default
  rw [← Global.IdeleGroup.coe_infiniteProj, this]
  simp [Global.posRealToUnits, Global.posRealElem, Global.RationalIdeles.isReal_infinitePlace]
  exact RingEquiv.apply_symm_apply (InfinitePlace.Completion.ringEquivRealOfIsReal _) r

theorem exists_centralSection_eq_realEmb (s : {r : ℝ // 0 < r}) :
    ∃ (r : ℝ) (hr : 0 < r), Reduction.centralSection ℚ 2 s = realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne')) := by
  set t := Reduction.rpowHom ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ s
  refine ⟨t.1, t.2, ?_⟩
  have hc : Reduction.centralSection ℚ 2 s =
      Reduction.diagUnits 2 (fun _ => Reduction.posIdele (K := ℚ) t.1 t.2) := rfl
  rw [hc]
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_realEmb]
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [Reduction.coe_diagUnits]
    change _ = Global.RationalIdeles.realEquiv.symm ((kGL (t.1 : ℂ) _ : Matrix (Fin 2) (Fin 2) ℝ) a b)
    rw [coe_kGL]
    fin_cases a <;> fin_cases b <;> simp [posIdele_fst_rat]
  · exact Reduction.prodEquiv_diagUnits_posIdele_snd (fun _ => t.1) (fun _ => t.2)

theorem apply_centralSection_mul {ψ : AdelicGL ℚ 2 → ℂ}
    (hψ : ∀ x (r : ℝ) (hr : 0 < r), ψ (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = ψ x)
    (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) : ψ (Reduction.centralSection ℚ 2 s * x) = ψ x := by
  obtain ⟨r, hr, hs⟩ := exists_centralSection_eq_realEmb s
  rw [Reduction.centralSection_mul_comm, hs, hψ _ _ hr]

def liftCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : cuspForms ℚ 2 :=
  ⟨(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ), liftEquiv_mem_cuspForms f⟩

def translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : Submodule ℂ (cuspForms ℚ 2) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRepCusp ℚ 2 g (liftCusp f))

theorem coe_mem_translateSpan (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {ψ : cuspForms ℚ 2}
    (hψ : ψ ∈ translateSpanCusp f) :
    (ψ : AdelicGL ℚ 2 → ℂ) ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem posScalar_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (x : AdelicGL ℚ 2) (r : ℝ) (hr : 0 < r) :
    (ψ : AdelicGL ℚ 2 → ℂ) (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = (ψ : AdelicGL ℚ 2 → ℂ) x := by
  rw [right_kGL_of_mem_translateSpan (liftEquiv N k f.toSlashInvariantForm).2.right_kGL
    (coe_mem_translateSpan f hψ)]
  have hs' : (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le, div_self (by exact_mod_cast hr.ne')]
  rw [hs', _root_.one_zpow, one_mul]

theorem centralSection_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) :
    (ψ : AdelicGL ℚ 2 → ℂ) (Reduction.centralSection ℚ 2 s * x) = (ψ : AdelicGL ℚ 2 → ℂ) x :=
  apply_centralSection_mul (posScalar_of_mem_translateSpanCusp f hψ) s x

end GL2Classical

end

end GroundTheory.Automorphic

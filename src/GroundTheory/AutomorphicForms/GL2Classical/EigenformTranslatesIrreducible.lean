import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter MeasureTheory
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm CuspidalSpectrum

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem coe_finRepCusp_apply (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) (x : AdelicGL ℚ 2) :
    ((finRepCusp ℚ 2 g ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) x = (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) :=
  rfl

theorem coe_rightTranslate_apply (y : AdelicGL ℚ 2) (ψ : AdelicGL ℚ 2 → ℂ) (x : AdelicGL ℚ 2) :
    Automorphic.rightTranslate y ψ x = ψ (x * y) :=
  rfl

variable (μ : Measure (Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure]

theorem cuspToL2_finRepCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (g : FiniteAdelicGL ℚ 2) :
    ∃ y : Reduction.normOneGL ℚ 2, ∀ ψ ∈ translateSpanCusp f,
      cuspToL2 μ (finRepCusp ℚ 2 g ψ) = cuspRep μ y (cuspToL2 μ ψ) := by
  have hex : ∃ (s : {r : ℝ // 0 < r}) (y : AdelicGL ℚ 2), y ∈ Reduction.normOneGL ℚ 2 ∧
      AutomorphicForm.finEmb ℚ 2 g = Reduction.centralSection ℚ 2 s * y :=
    CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL _
  obtain ⟨s, y, hy, hxy⟩ := hex
  refine ⟨⟨y, hy⟩, fun ψ hψ => ?_⟩
  refine cuspToL2_rightTranslate μ ⟨y, hy⟩ ψ (finRepCusp ℚ 2 g ψ) ?_
  funext x
  rw [coe_finRepCusp_apply, coe_rightTranslate_apply]
  change (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) = (ψ : AdelicGL ℚ 2 → ℂ) (x * y)
  rw [hxy, ← mul_assoc, ← Reduction.centralSection_mul_comm, mul_assoc,
    centralSection_of_mem_translateSpanCusp f hψ]

theorem eq_zero_of_cuspFormLp_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {v : cuspForms ℚ 2} (hv : v ∈ translateSpanCusp f) (h0 : cuspToL2 μ v = 0) : v = 0 :=
  injOn_cuspToL2 μ (fun s x => centralSection_of_mem_translateSpanCusp f hv s x)
    (fun _ _ => rfl) (h0.trans (map_zero _).symm)

variable (k) in

def descendL : cuspForms ℚ 2 →ₗ[ℂ] (ℍ → ℂ) where
  toFun ψ := descend k ψ
  map_add' ψ ψ' := by funext z; simp [descend, mul_add]
  map_smul' c ψ := by funext z; simp [descend]; ring

open Classical in

def heckeFin (N p : ℕ) [NeZero p] : Finset (FiniteAdelicGL ℚ 2) :=
  (heckeReps N p).image (finiteDiagonal ℚ 2)

end GL2Classical

end

end GroundTheory.Automorphic

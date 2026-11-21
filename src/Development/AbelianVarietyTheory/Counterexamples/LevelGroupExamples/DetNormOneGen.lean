import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet

noncomputable section

namespace GlobalTheory.LevelSubgroup

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem det_norm_one_gen {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B → B) (φ : A →+* B)
    (hφ : ∀ x, τ (φ x) = φ (σ x)) (J g : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (h : Formalism.UG.cT σ g * J * g = J) : (g.map φ).det * τ (g.map φ).det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (RingHom.map_det _ _).symm
  have h5 : (g.map φ).det = φ g.det := (RingHom.map_det _ _).symm
  rw [h2] at h1
  have h4 : g.det * σ g.det = 1 := by
    apply hJ.mul_left_cancel
    linear_combination h1
  rw [h5, hφ, ← map_mul, h4, map_one]

theorem isUnit_det_JR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) : IsUnit (JR (F := F) (AF F) J).det := by
  have h3 : (JR (F := F) (AF F) J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
  rw [h3]
  exact (Ne.isUnit h).map _

end GlobalTheory.LevelSubgroup

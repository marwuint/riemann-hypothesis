import Mathlib
import Formalism.LocalToGlobal.Columns.BrpAevalScaleMonomial
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv

open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Loc

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem localization_map₃ (p : Ideal (𝓞 K)) [p.IsPrime] (f : V →ₗ[K] V') (A : Submodule (𝓞 K) V) :
    localization₂ p (A.map (f.restrictScalars (𝓞 K))) = (localization₂ p A).map (f.restrictScalars (𝓞 K)) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by exact_mod_cast h0
      rw [this]; exact p.zero_mem
    refine ⟨((s : K)⁻¹) • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul]
      rw [show (algebraMap (𝓞 K) K s) * (s : K)⁻¹ = 1 from mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · simp only [LinearMap.restrictScalars_apply, map_smul]
      simp only [LinearMap.restrictScalars_apply] at hax
      rw [hax, ← algebraMap_smul K s x, smul_smul]
      rw [show (s : K)⁻¹ * (algebraMap (𝓞 K) K s) = 1 from inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    simp only [LinearMap.restrictScalars_apply]
    rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]

end Loc

section LocDel

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpRhoEquiv (lam : DomWeight n) (B : GL (Fin n) K) : VV K (oneW lam) ≃ₗ[K] VV K (oneW lam) :=
  LinearEquiv.ofLinear (rhoK (oneW lam) (fun _ => B)) (rhoK (oneW lam) (fun _ => B⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B) * fun _ => B⁻¹) = 1 := by funext; simp
      rw [this, map_one]; rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B⁻¹) * fun _ => B) = 1 := by funext; simp
      rw [this, map_one]; rfl)

def brpMatEquiv (B : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (B : Matrix (Fin n) (Fin n) K)) (Matrix.mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.mulVecLin_mul]; simp)
    (by rw [← Matrix.mulVecLin_mul]; simp)

theorem brp_lidx_colLat (M : Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K)
    (hB : IsBasisAt w M B) :
    lidx w.asIdeal (colLat (1 : GL (Fin n) K)) M = vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
  rw [bridge_lidx_det_holds K (Fin n → K) w (colLat 1) M (brpMatEquiv K B) (brz_colLat_one_lattice K) ?_]
  · show vAdd w (LinearMap.det (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))) = _
    rw [LinearMap.det_toLin']
  · rw [hB, lc_colLat_eq_gLat B]
    rfl

end LocDel

section Weyl

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem brp_span_lattice {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {j : ℕ}
    (e : Fin j → V) (hsp : Submodule.span K (Set.range e) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower]
  exact hsp

theorem brp_colLat_one_span (n : ℕ) :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K)) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem brp_lcvInf_std (n : ℕ) :
    Formalism.LFunctionChainParameters.LLcv.lcvInf (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 0 := by
  unfold Formalism.LFunctionChainParameters.LLcv.lcvInf
  have : ∀ v, gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 1 := by
    intro v
    ext a c
    simp only [gramPl, Matrix.of_apply, majAt, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = c
      · subst h; simp
      · simp [Pi.single_apply, Matrix.one_apply, h, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [this]

end Weyl

end Formalism.L2.Col

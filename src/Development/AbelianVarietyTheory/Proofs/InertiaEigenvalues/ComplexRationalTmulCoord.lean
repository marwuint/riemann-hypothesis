import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ThetaRank

section Class

structure ClassDat (A K M W : Type) [CommRing A] [Field K] [Algebra A K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module A W] where
  Hf : Type
  [grp : Group Hf]
  HF : Subgroup Hf
  J : Subgroup Hf
  lam : J →* Aˣ
  PP : Type
  [acg : AddCommGroup PP]
  [modK : Module K PP]
  [modA : Module A PP]
  [tow : IsScalarTower A K PP]
  rho : HF →* (PP ≃ₗ[K] PP)
  LL : Hf → Submodule A PP
  reps : Finset Hf
  reps_cover : ∀ h, ∃ r ∈ reps, ∃ (γ : HF) (k : J), h = γ * r * k
  reps_sep : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ (γ : HF) (k : J), r' = γ * r * k → r' = r
  ev : M →ₗ[A] (Hf → PP)
  ev_inj : Function.Injective ev
  ev_law : ∀ f (γ : HF) h (k : J), ev f (γ * h * k) = ((lam k : Aˣ) : A) • rho γ (ev f h)
  ser : Hf → PP →ₗ[A] W

attribute [instance] ClassDat.grp ClassDat.acg ClassDat.modK ClassDat.modA ClassDat.tow

namespace ClassDat

end ClassDat

end Class

section Cx

structure CxDat (A M W : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module A W] where
  [alg : Algebra A ℂ]
  inj : Function.Injective (algebraMap A ℂ)
  MC : Type
  [nM : NormedAddCommGroup MC]
  [iM : InnerProductSpace ℂ MC]
  [fM : FiniteDimensional ℂ MC]
  cM : ℂ ⊗[A] M ≃ₗ[ℂ] MC
  WC : Type
  [nW : NormedAddCommGroup WC]
  [iW : InnerProductSpace ℂ WC]
  [fW : FiniteDimensional ℂ WC]
  cW : ℂ ⊗[A] W ≃ₗ[ℂ] WC
  Rep : Type
  part : Rep → Submodule ℂ WC
  good : Set Rep

attribute [instance] CxDat.nM CxDat.iM CxDat.fM CxDat.nW CxDat.iW CxDat.fW

namespace CxDat

variable {A M W : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module A W] (Z : CxDat A M W)

def mapC (θ : M →ₗ[A] W) : Z.MC →ₗ[ℂ] Z.WC :=
  letI := Z.alg
  Z.cW.toLinearMap ∘ₗ θ.baseChange ℂ ∘ₗ Z.cM.symm.toLinearMap

end CxDat

end Cx

namespace Model

theorem tmul_rat (z : ℂ) (q : ℚ) : z ⊗ₜ[ℤ] q = (z * q) ⊗ₜ[ℤ] (1 : ℚ) := by
  have hd : ((q.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have h1 : z = (q.den : ℤ) • (z / ((q.den : ℤ) : ℂ)) := by rw [zsmul_eq_mul]; field_simp
  have h2 : (q.den : ℤ) • q = q.num • (1 : ℚ) := by simp
  have h3 : z * q = q.num • (z / ((q.den : ℤ) : ℂ)) := by
    rw [zsmul_eq_mul, Rat.cast_def]; push_cast; ring
  rw [h3, TensorProduct.smul_tmul, ← h2, ← TensorProduct.smul_tmul, ← h1]

def cq : ℂ ⊗[ℤ] ℚ ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofLinear (((Algebra.linearMap ℚ ℂ).restrictScalars ℤ).liftBaseChange ℂ)
    (LinearMap.toSpanSingleton ℂ _ ((1 : ℂ) ⊗ₜ[ℤ] (1 : ℚ))) (by ext; simp) (by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
      | tmul z q =>
        rw [LinearMap.id_apply, tmul_rat z q]
        simp [TensorProduct.smul_tmul'])

def c2 : ℂ ⊗[ℤ] (Fin 2 → ℚ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (TensorProduct.piRight ℤ ℂ ℂ fun _ : Fin 2 => ℚ) ≪≫ₗ (LinearEquiv.piCongrRight fun _ => cq) ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).symm

def lat : Submodule ℤ (Fin 2 → ℚ) := Submodule.pi Set.univ fun _ => (1 : Submodule ℤ ℚ)

def cls : ClassDat ℤ ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) where
  Hf := Multiplicative (ZMod 2)
  HF := ⊤
  J := ⊤
  lam := 1
  PP := Fin 2 → ℚ
  rho := 1
  LL _ := lat
  reps := {1}
  reps_cover h := ⟨1, Finset.mem_singleton_self _, ⟨h, trivial⟩, 1, by simp⟩
  reps_sep r hr r' hr' _ _ _ := by rw [Finset.mem_singleton.1 hr, Finset.mem_singleton.1 hr']
  ev := LinearMap.pi fun _ => LinearMap.id
  ev_inj _ _ h := congrFun h 1
  ev_law _ _ _ _ := by simp
  ser _ := (2 : ℤ) • LinearMap.id

abbrev cx : CxDat ℤ (Fin 2 → ℚ) (Fin 2 → ℚ) where
  inj := Int.cast_injective
  MC := EuclideanSpace ℂ (Fin 2)
  cM := c2
  WC := EuclideanSpace ℂ (Fin 2)
  cW := c2
  Rep := Fin 2
  part a := ℂ ∙ EuclideanSpace.single a (1 : ℂ)
  good := {0}

def pr : (Fin 2 → ℚ) →ₗ[ℤ] (Fin 2 → ℚ) := LinearMap.single ℤ (fun _ : Fin 2 => ℚ) 0 ∘ₗ LinearMap.proj 0

end Model

end GlobalTheory.ThetaRank

end

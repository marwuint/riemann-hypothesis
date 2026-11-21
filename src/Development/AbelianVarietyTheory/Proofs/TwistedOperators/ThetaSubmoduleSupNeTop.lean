import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.ThetaGLSub
open scoped TensorProduct

namespace GlobalTheory.ThetaGLSub.SumProper

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def rhoS : Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om 1 g (1 : GL (Fin n) k) Φ, Model.om_mem_SB 1 g 1 Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (by exact om_add 1 g 1 (Φ : Matrix (Fin n) (Fin m) k → ℂ) Ψ)
      map_smul' := fun c Φ => Subtype.ext (by exact om_smul 1 g 1 c (Φ : Matrix (Fin n) (Fin m) k → ℂ)) }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (Model.om_one 1 Φ.1)
  map_mul' a b := LinearMap.ext fun Φ => Subtype.ext (by
    have := Model.om_mul (1 : kˣ →* ℂˣ) a b (1 : GL (Fin n) k) 1 Φ.1
    rw [mul_one] at this
    exact this)

@[simp] theorem rhoS_apply (g : GL (Fin m) k) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    ((rhoS k n m g Φ : SB (Matrix (Fin n) (Fin m) k)) : Matrix (Fin n) (Fin m) k → ℂ) =
      om 1 g (1 : GL (Fin n) k) Φ := rfl

def res (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Submodule ℂ (SB (Matrix (Fin n) (Fin m) k)) :=
  M.comap (SB _).subtype

theorem mem_res {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} {Φ : SB (Matrix (Fin n) (Fin m) k)} :
    Φ ∈ res M ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M := Iff.rfl

def rhoQ (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) :
    Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) where
  toFun g := (res M).mapQ (res M) (rhoS k n m g) (fun Φ hΦ => hM g Φ hΦ)
  map_one' := by
    apply Submodule.linearMap_qext
    ext Φ
    simp
  map_mul' a b := by
    apply Submodule.linearMap_qext
    ext Φ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, map_mul, Module.End.mul_apply]
    rfl

theorem rhoQ_mk (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) (g : GL (Fin m) k)
    (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    rhoQ M hM g ((res M).mkQ Φ) = (res M).mkQ (rhoS k n m g Φ) := rfl

variable {χ : GL (Fin n) k →* ℂˣ}

def tmap (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] ℂ :=
  (TensorProduct.mk ℂ V ℂ).flip 1 ∘ₗ e ∘ₗ (res M).mkQ

theorem tmap_apply (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    tmap M e Φ = e ((res M).mkQ Φ) ⊗ₜ[ℂ] (1 : ℂ) := rfl

end GlobalTheory.ThetaGLSub.SumProper

namespace GlobalTheory.ThetaGLSub.SumProper

end GlobalTheory.ThetaGLSub.SumProper

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

set_option autoImplicit false

noncomputable section

open Coalgebra

namespace GlobalTheory.HTPair

open GlobalTheory.PDiv

structure QuotTower {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) : Type 1 where

  B : ℕ → Type
  [commRing : ∀ m, CommRing (B m)]
  [hopf : ∀ m, HopfAlgebra O (B m)]
  [cocomm : ∀ m, IsCocomm O (B m)]
  [finite : ∀ m, Module.Finite O (B m)]
  [projective : ∀ m, Module.Projective O (B m)]

  j : ∀ m, B m →ₐc[O] G.A (m + 1)

  ρ : ∀ m, G.A (m + 1) →ₗ[O] B m

  r : ∀ m, B (m + 1) →ₐc[O] B m

  s : ∀ m, G.A m →ₐc[O] B m

  ρ_j : ∀ m b, ρ m (j m b) = b

  r_surjective : ∀ m, Function.Surjective (r m)

  j_r : ∀ m b, j m (r m b) = G.res (m + 1) (j (m + 1) b)

  j_s : ∀ m a, j m (s m a) = G.mulP m a

  tors_le : ∀ m, torsionIdeal O (G.A (m + 1)) p ≤ kerIdeal (j m)

attribute [instance] QuotTower.commRing QuotTower.hopf QuotTower.cocomm QuotTower.finite
  QuotTower.projective

theorem exists_retraction_mulP {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (m : ℕ) :
    ∃ ρ : G.A (m + 1) →ₗ[O] G.A m, ∀ a, ρ (G.mulP m a) = a := by
  let f : G.A m →ₗ[O] G.A (m + 1) := (G.mulP m : G.A m →ₐ[O] G.A (m + 1)).toLinearMap
  have hs : Function.Surjective f.dualMap := fun φ => by
    obtain ⟨ψ, hψ⟩ := G.dual_mulP_surjective m (WithConv.toConv φ)
    exact ⟨ψ.ofConv, congrArg WithConv.ofConv hψ⟩
  obtain ⟨σ, hσ⟩ := f.dualMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨(Module.evalEquiv O (G.A m)).symm.toLinearMap ∘ₗ σ.dualMap ∘ₗ
    (Module.evalEquiv O (G.A (m + 1))).toLinearMap, fun a => ?_⟩
  change (Module.evalEquiv O (G.A m)).symm _ = a
  rw [LinearEquiv.symm_apply_eq]
  ext φ
  exact LinearMap.congr_fun (LinearMap.congr_fun hσ φ) a

theorem QuotTower.map_res_kerIdeal {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O}
    (T : QuotTower G) (m : ℕ) :
    Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1)) (kerIdeal (T.j (m + 1))) =
      kerIdeal (T.j m) := by
  have h : (G.res (m + 1)).comp (T.j (m + 1)) = (T.j m).comp (T.r m) :=
    BialgHom.ext fun b => (T.j_r m b).symm
  rw [← kerIdeal_comp, h, kerIdeal_comp_of_surjective (T.j m) (T.r_surjective m)]

end GlobalTheory.HTPair

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace PositivityTheory.ThKW.RealC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPart_tmul (a : AF F) (x : E) : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl

theorem theta_inc {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (x : E) :
    θ (infPartF F E (incAF F E x)) = τ x := by
  have : infPartF F E (incAF F E x) = fstA F 1 ⊗ₜ[F] x := rfl
  rw [this, map_one, h.1]

theorem continuous_theta {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) :
    Continuous (θ.comp (infPartF F E)) := by
  haveI := isModuleTopology_AE F E
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  exact h.2.comp (continuous_fst (X := Ainf F) (Y := Af F))

theorem herm_map {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, map_apply, map_apply, ← hτ, hJ.1]

theorem unit_map {σ : E →ₐ[F] E} (τ : E →+* ℂ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsUnit (J.map τ).det := by
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [this]
  exact ((map_ne_zero τ).2 hJ.2).isUnit

theorem re_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hσ : σ ξ = -ξ) :
    (τ ξ).re = 0 := by
  have := congrArg Complex.re (hτ ξ)
  rw [hσ, map_neg] at this
  simp at this
  linarith

theorem im_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hξ : ξ ≠ 0) (hσ : σ ξ = -ξ) :
    (τ ξ).im ≠ 0 := fun h => (map_ne_zero τ).2 hξ (Complex.ext (re_xi hτ hσ) h)

end PositivityTheory.ThKW.RealC

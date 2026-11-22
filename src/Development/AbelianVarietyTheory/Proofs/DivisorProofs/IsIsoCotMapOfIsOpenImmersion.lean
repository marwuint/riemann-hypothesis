import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add, map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

end GlobalTheory.TorusPart

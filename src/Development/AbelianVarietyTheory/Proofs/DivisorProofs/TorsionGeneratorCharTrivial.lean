import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := _root_.GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (_root_.GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory

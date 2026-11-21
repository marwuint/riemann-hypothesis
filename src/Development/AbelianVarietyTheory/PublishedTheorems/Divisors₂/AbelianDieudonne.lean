import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : ∀ (A : Over (Sp k)) [GrpObj A], ModuleCat.{0} (WittVector p k))
      (map : ∀ {A B : Over (Sp k)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f],
        M A →ₗ[WittVector p k] M B)
      (F : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M A)
      (V : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M A)
      (red : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      (∀ (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
        SmoothOfRelativeDimension g A.hom →
        Module.Free (WittVector p k) (M A) ∧ Module.Finite (WittVector p k) (M A) ∧
        Module.finrank (WittVector p k) (M A) = 2 * g ∧
        (∀ m, F A (V A m) = p • m) ∧ (∀ m, V A (F A m) = p • m) ∧
        Function.Surjective (red A) ∧ (∀ m, red A m = 0 ↔ ∃ n, m = p • n) ∧
        (∀ h, h ∈ Fil A ↔ ∃ m, h = red A (V A m)) ∧
        map (𝟙 A) = LinearMap.id) ∧
      (∀ (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
        (∀ (f : A ⟶ B) [IsMonHom f] (m : M A),
          map f (F A m) = F B (map f m) ∧ map f (V A m) = V B (map f m) ∧
          red B (map f m) = push (dp0 k) (𝟙 _) f (red A m)) ∧
        ∀ (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)],
          map (f * g) = map f + map g) ∧
      ∀ (A B C : Over (Sp k)) [GrpObj A] [GrpObj B] [GrpObj C], IsAbelianScheme A →
        IsAbelianScheme B → IsAbelianScheme C →
        ∀ (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g], map (f ≫ g) = map g ∘ₗ map f

namespace AbelianDieudonne

end AbelianDieudonne

end GlobalTheory.Published

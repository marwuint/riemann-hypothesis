import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveDescentOfAffineOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_fibreSquare_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y := by
  intro R _ S Y Z π y p q H r h1 h2
  have A : IsPullback (pullback.fst p p ≫ q) (pullback.snd p p) π (p ≫ y) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback p p) H.flip
  have X : IsPullback r (pullback.snd p p) (pullback.snd π π) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst π π) ?_ h2 (IsPullback.of_hasPullback π π)
    rw [h1, ← H.w]; exact A
  have := IsPullback.paste_vert X H.flip
  rwa [pullback.condition (f := p), pullback.condition (f := π)]

theorem descend_of_equalised_fibreSquare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ _ _ _ S Y Z π y p q hπ hs hS hy H
  have hinj := _root_.GlobalTheory.appTop_injective_of_surjective_toSpec_domain R S π hs hS
  have heq := _root_.GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd R S π hπ hS hinj
  let r : pullback p p ⟶ pullback π π := pullback.map p p π π q q y H.w H.w
  have h1 : r ≫ pullback.fst π π = pullback.fst p p ≫ q := pullback.lift_fst _ _ _
  have h2 : r ≫ pullback.snd π π = pullback.snd p p ≫ q := pullback.lift_snd _ _ _
  have hP := isPullback_fibreSquare_baseChange R S Y Z π y p q H r h1 h2
  exact _root_.GlobalTheory.Mum.app_injective_and_descent_of_affineOpens Y Z p fun V hV => ⟨GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper R S Y Z π y p q hπ hy H hinj V hV,
    _root_.GlobalTheory.Mum.AffDesc.mem_range_app_of_flat R S Y Z π y p q hπ hy H r h1 h2 hP heq V hV⟩

end GlobalTheory

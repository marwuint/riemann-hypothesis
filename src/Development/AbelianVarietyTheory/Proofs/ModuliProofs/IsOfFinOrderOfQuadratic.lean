import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

end Unif

end GlobalTheory.CMSpreadCompare

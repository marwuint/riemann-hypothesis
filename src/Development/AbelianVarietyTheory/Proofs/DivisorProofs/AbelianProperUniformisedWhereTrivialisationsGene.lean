import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnits

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem abelian_and_proper_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G ∧ IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hB D A G _ _ hG U W hW
  exact ⟨_root_.GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn R hB D A G hG U W hW, _root_.GlobalTheory.UnifProperOpen.isProper_restrict R hB D A G hG U W (_root_.GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn R hB D A G hG U W hW)⟩

end GlobalTheory.Mum

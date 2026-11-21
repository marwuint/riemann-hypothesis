import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionClassifyingFamilyChart

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem fieldChart_of_inj : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (U : Over S) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom →
    Fam A M → Inj A M → FieldChart A M := by
  intro S A _ hA g hg U M hU hM hI K _ _ s T t N hN
  obtain ⟨B, b, P, hP, hgood⟩ := _root_.GlobalTheory.DualCon.FieldRep.hasRep_field S A hA g hg K s
  obtain ⟨φ, hφb, hφS, hφm⟩ := _root_.GlobalTheory.DualCon.classify_mono S A B (Over.mk s) U b P M hP hM hI
  have hpb : IsPullback (fst U (Over.mk s)).left (snd U (Over.mk s)).left U.hom (Over.mk s).hom :=
    .of_hasPullback _ _
  have hsnd : SmoothOfRelativeDimension g (snd U (Over.mk s)).left :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpb hU
  have hcomp : SmoothOfRelativeDimension g (φ.left ≫ b.left) := by
    rw [← Over.comp_left, hφb]; exact hsnd
  have hopen : IsOpenImmersion φ.left :=
    _root_.GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension _ _ _ φ.left b.left g hgood.smooth hcomp hφm
  exact _root_.GlobalTheory.RepChart.repChart S A B (Over.mk s) U b P M hP hM φ hφb hφS hopen T t N hN

end GlobalTheory.DualOpen

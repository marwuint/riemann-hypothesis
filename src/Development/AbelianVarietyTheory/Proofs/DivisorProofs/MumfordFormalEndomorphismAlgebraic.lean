import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatiosStatement
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := _root_.GlobalTheory.MumSec.main R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := _root_.GlobalTheory.Mum.GenericRatio.exists_generic_hom R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := _root_.GlobalTheory.Mum.semiAbelian_end_generic_extends R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum

import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailRest
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOriginNormalisationUnitAtTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_secs_of_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ :=
  GlobalTheory.Mum.SecsDesc.assemble _root_.GlobalTheory.Mum.exists_map_exp_all_traits _root_.GlobalTheory.Mum.exists_unit_normalisation _root_.GlobalTheory.Mum.exists_theta_unit_at_traits

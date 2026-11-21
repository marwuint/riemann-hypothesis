import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreThetaEmbeddingOfSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_emb_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C
  obtain ⟨R₁, i₁, i₂, i₃, ρ, D₁, C₁, hρ, hD, hS⟩ := _root_.GlobalTheory.Mum.exists_secs_finExt R hR D C
  have := hR.2
  have h₁ : Base R₁ := ⟨hρ.1, (RingHom.charZero_iff hρ.2.1).1 this⟩
  obtain ⟨C', E, hE⟩ := _root_.GlobalTheory.Mum.SecEmb.emb_of_secs R₁ h₁ D₁ C₁ hS
  exact ⟨R₁, i₁, i₂, i₃, ρ, D₁, C', E, hρ, hD, hE⟩

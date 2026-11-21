import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibresCommonPullDegToField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumRig.exists_common_pull_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, Nonempty (IsPullDeg φ D₁.toPre D') → Nonempty (IsPullDeg φ D₂.toPre D') → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₃ : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₁.toPre D₃.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) := by
  intro R _ _ _ hR D₁ D₂ W _ _ φ hφ D' ⟨h₁⟩ ⟨h₂⟩
  obtain ⟨E₁, E₂, L, _, β, E', ⟨e₁⟩, ⟨e₂⟩, ⟨f₁⟩, ⟨f₂⟩⟩ := _root_.GlobalTheory.Mum.exists_generic_common_pull R hR D₁ D₂ W φ hφ D' h₁ h₂
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, E₃, hio, ⟨g₁⟩, ⟨g₂⟩⟩ := _root_.GlobalTheory.FieldDesc.exists_finite_common_pull (FractionRing R) L β E₁ E₂ E' f₁ f₂
  obtain ⟨R', _, _, _, ρ, E, hfin, hloc, ⟨k₁⟩, ⟨k₂⟩⟩ := _root_.GlobalTheory.CommonCover.exists_common_pull R hR D₁.toPre D₂.toPre E₁ E₂ e₁ e₂ K' io E₃ hio g₁ g₂
  obtain ⟨D₃, ⟨p⟩⟩ := GlobalTheory.MumPull.exists_pull R R' ρ hfin.2.1 hloc D₁
  exact ⟨R', _, _, _, ρ, D₃, hfin, ⟨p⟩, _root_.GlobalTheory.Mum.isPullDeg_of_generic R R' ρ hfin.1 hfin.2.1 D₁.toPre D₂.toPre D₃.toPre E p k₁ k₂⟩

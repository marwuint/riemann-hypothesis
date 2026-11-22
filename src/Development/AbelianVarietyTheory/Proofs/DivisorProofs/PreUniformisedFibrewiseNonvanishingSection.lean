import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := _root_.GlobalTheory.Mum.TraitCompare.exists_cmp_under R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := _root_.GlobalTheory.Mum.exists_coefData_of_ne_zero R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.SecDiv.exists_expT_of_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (_root_.GlobalTheory.PreUTheta.exists_mem_nonzeroLocus R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum

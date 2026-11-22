import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_hasFin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  intro R _ _ _ hR D ⟨R', _, _, _, ρ, D', hρ, ⟨p⟩, hH⟩
  obtain ⟨R'', _, _, _, σ, hσ, hσl, hc, hg⟩ := _root_.GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom R R' ρ hR hρ
  obtain ⟨D'', ⟨q⟩⟩ := _root_.GlobalTheory.MumPull.exists_pull R' R'' σ hσ.2.1 hσl D'
  obtain ⟨G'', _, _, A'', hG, ⟨U⟩⟩ := _root_.GlobalTheory.Mum.has_pull R' R'' σ hρ.1 hσ.1 hσ.2.1 hσl D' D'' ⟨q⟩ hH
  obtain ⟨r⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q
  obtain ⟨act⟩ := _root_.GlobalTheory.Mum.galAct_exists R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U
  exact _root_.GlobalTheory.Mum.has_of_galois_action R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U act

end GlobalTheory.Mum

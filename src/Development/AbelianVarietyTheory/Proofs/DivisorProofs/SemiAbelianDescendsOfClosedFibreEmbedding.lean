import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpDescent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' E hθ
  have : IsNoetherianRing R := hR.1
  have : IsIntegrallyClosed R := hR.2.2.1
  have hs : Surjective M.π := (Modif.appTop_bijective_surjective R M).2
  obtain ⟨N, fU, l, hl, hf⟩ := _root_.GlobalTheory.Mum.exists_near R hR M G' hG' E
  have hN : N.Law := _root_.GlobalTheory.Mum.Near.law_of_emb R hR M G' hG' E N fU l hl hf
  obtain ⟨G, i1, i2, β, i, hG, hβ, hi, hu⟩ := _root_.GlobalTheory.Mum.descend_of_near R hR M.S M.π M.proper hs M.integral G' hG' N hN
  obtain ⟨θ, O, hO, hθO⟩ := _root_.GlobalTheory.Mum.exists_open_theta_descent R M.S M.π hs G' E N fU l hl hf P'.L.L hθ G β i hβ.1.w hi hu
  obtain ⟨L, hL, hLi⟩ := _root_.GlobalTheory.Mum.CubeDesc.cubicalBundle_descends R hR M G' hG' P' G β hG hβ θ O hO hθO
  obtain ⟨P, rfl⟩ := _root_.GlobalTheory.Mum.exists_cp_descent R hR M G' hG' P' G β hG hβ L hL hLi
  exact ⟨G, i1, i2, P, β, hG, hβ, hLi⟩

end GlobalTheory.Mum

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionNbhdIsolatedFibrePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianProjectiveSpaceAndPullbackProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingLiftSeparatedFiniteTypeQuasi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftGeometricPointOverClosedFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem closedFibre_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsNoetherian P' ∧ IsSeparated b ∧ LocallyOfFiniteType b ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ a ≫ b = X.ι ≫ E.f ∧ (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) ∧ ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hR M G' _ _ hG E
  haveI : IsNoetherianRing R := hR.1
  haveI := M.proper
  obtain ⟨hPn, hTn⟩ := _root_.GlobalTheory.Mum.pspace_noeth_and_pullback R M.S M.π M.proper E.N
  obtain ⟨hs, hl, hq⟩ := _root_.GlobalTheory.Mum.emb_lift_sep_loft_qc R hR M G' hG E
  obtain ⟨H', X'', ν, i, hZ, hν, hi, hiν, -, -⟩ := _root_.GlobalTheory.ZmtNbhd.exists_finite_openImmersion_nbhd E.H.toScheme _
    (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) hTn hs hl hq
    {z | M.π (G'.hom (E.H.ι z)) = closedPoint R} (fun z hz => ⟨⊤, trivial, fun w _ hw => _root_.GlobalTheory.Mum.Emb.chart_injective R hR M G' hG E z w hz hw⟩)
  haveI := hν; haveI := hi; haveI := hPn
  have hprop : IsProper (ν ≫ pullback.fst (PSpace.str R E.N) M.π) := inferInstance
  obtain ⟨P'', a'', b'', hab, hb'', ha'', hsurj, hbij, hconn⟩ :=
    _root_.GlobalTheory.SteinFact.stein_factorisation X'' (PSpace R E.N) _ inferInstance hprop
  haveI := hb''
  obtain ⟨P', c, X, k, a, hc, hP', hpa, hsa, hba, hk, hac, hsat, -⟩ :=
    _root_.GlobalTheory.restrict_proper_sections_bijective_to_fibre_open (PSpace R E.N) E.H.toScheme X'' P'' H' i a'' b'' hPn hi ha'' hsurj hbij hb''
  haveI := hc
  have hf : a ≫ c ≫ b'' = X.ι ≫ E.f := by
    rw [← Category.assoc, hac, Category.assoc, Category.assoc, hab, ← Category.assoc i, hiν, ← hk]
    simp only [Category.assoc]
    erw [pullback.lift_fst]
  have hX : ∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X := by
    intro z hz
    have hz' : z ∈ H' := hZ hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range H'.ι := by rwa [Scheme.Opens.range_ι]
    exact hsat z' (_root_.GlobalTheory.Mum.steinFibre_subset_range R hR M G' hG E H' X'' ν i P'' a'' b'' hν hi hiν hab hb'' ha'' hconn (fun h hh => hZ hh) z' hz)
  refine ⟨P', c ≫ b'', X, a, hP', inferInstance, inferInstance, hpa, hsa, hba, hf, hX, ?_⟩
  exact _root_.GlobalTheory.Mum.Emb.lift_closedPoint R hR M G' hG E P' (c ≫ b'') X a inferInstance hsa hf hX

end GlobalTheory.Mum

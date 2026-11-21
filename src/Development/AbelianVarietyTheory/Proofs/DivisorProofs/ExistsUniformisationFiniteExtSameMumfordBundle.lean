import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGenericFibreExtendsOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UExt

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q f f rfl)

end GlobalTheory.Mum.UExt

open GlobalTheory.Mum.UExt in

theorem GlobalTheory.Mum.exists_unif_finExt_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨hdvr, hcomp, hchar⟩ := hR
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  have hL : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  obtain ⟨L', hL', hLL'⟩ := _root_.GlobalTheory.Mum.lb_extends_over_dvr R G (A.L.pull gen.hom.left) hL
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    _root_.GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen.hom hgen A.L _ A.isLB (pull_isLB hL' _) A.sym hLL'
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R G hG hpr L' hL' hsym
  subst hP
  obtain ⟨R', _, _, _, ρ, G₁, _, _, β, β₂, P₁, A₁, gen₁, hR', hρ, hβ, hsq, hgen₁, hL₁, hLam, hEven⟩ :=
    _root_.GlobalTheory.Mum.exists_even_translate R ⟨hdvr, hcomp, hchar⟩ G hG P A gen hgen hLL'
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hchar⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap ρ) G hG)
  obtain ⟨D, U, hU, -⟩ := _root_.GlobalTheory.Mum.exists_unif_even R' hB' G₁ P₁ hG₁ hEven A₁ gen₁ hgen₁ hL₁
  have hE : LBIso (abelian₂ G P.L.L) PP := _root_.GlobalTheory.Mum.lbIso_lam_of_extLam R G hG P.L.L _ PP P.L.isLB hL hLL' hPP
  refine ⟨R', _, _, _, ρ, D, G₁, _, _, β, β₂, A₁, U, hR', hρ, hβ, hsq, ?_⟩
  rw [hU]
  exact LBIso.trans (lam_isLB G₁ P₁.L.isLB) (pull_isLB (lam_isLB G P.L.isLB) _) (pull_isLB hPP.1 _) hLam
    (lbIso_pull hE β₂)

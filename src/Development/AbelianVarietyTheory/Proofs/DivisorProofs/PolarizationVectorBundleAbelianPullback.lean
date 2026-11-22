import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt.Fibre

section Frames

variable {X Y : Scheme.{0}} {I : Type} [Fintype I] {k : Type} [CommRing k]

theorem frame_pb (f : Y ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
    {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
  have := (he.pullback f).res h
  exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ this

end Frames

section Tangent

open GlobalTheory.HodgeSub.Nat GlobalTheory.TanFibre GlobalTheory.Conormal
open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

theorem omegaBase_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (h' : IsGrpPullback G'' G' f' φ') {f'' : S'' ⟶ S} {φ'' : G''.left ⟶ G.left}
    (h'' : IsGrpPullback G'' G f'' φ'') (e : f' ≫ f = f'') (e' : φ' ≫ φ = φ'') {U : S.Opens} {V : S'.Opens}
    {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V) (hW' : W ≤ f'' ⁻¹ᵁ U) (s : Γ(omega G, U)) :
    (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) =
      (omegaBase h'').app W (pullbackSections f'' _ hW' s) := by
  subst e e'
  have k {U : S.Opens} {V : S'.Opens} {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V)
      (hW' : W ≤ (f' ≫ f) ⁻¹ᵁ U) (s : Γ(omega G, U)) :
      ((Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
        omegaBase h').app W (pullbackSections (f' ≫ f) _ hW' s) =
      (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) := by
    rw [← QCoh.app_app, ← QCoh.app_app, Vert.DivPull.pullbackComp_inv_app f' f _ hV hW]
    exact congrArg _ (QCoh.pullback_map_app_pullbackSections f' _ _ _)
  have : (Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
      omegaBase h' = omegaBase h'' := by
    refine pullback_hom_ext (sec_hom η[G]) fun W a => ?_
    have k₁ := le_of_sq (unitSec_comp h) (le_refl (unitSec G ⁻¹ᵁ W)) le_rfl
    have k₂ := le_of_sq (unitSec_comp h') k₁ le_rfl
    refine (k le_rfl le_rfl le_rfl (dUnit G le_rfl a)).trans ?_
    rw [omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl, omegaBase_dUnit h' k₁ le_rfl k₂ le_rfl]
    exact (congrArg _ (appLE_appLE rfl _ _ le_rfl a)).trans (omegaBase_dUnit h'' le_rfl le_rfl k₂ le_rfl a).symm
  rw [← this, k hV hW]

variable {k : Type} [CommRing k] {C : Scheme.{0}} {G : Over C} [GrpObj G] {x : Sp k ⟶ C} {B : Over (Sp k)} [GrpObj B]
  {ψ : B.left ⟶ G.left}

end Tangent

open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DualPull (theta dualApp_theta)

end GlobalTheory.BadPt.Fibre

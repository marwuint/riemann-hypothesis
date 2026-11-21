import Mathlib
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.ConnectedSpaceTorus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.NotExistsEvenTwistSymOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrivDescentCompare

section General

theorem smooth_conn {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S}
    [GrpObj G] (Q : TQ G X) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  have := Q.q_hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have hs := Q.smooth_proj_of_free
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  have sq := (H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)
  have hc : GeometricallyConnected Q.q.left := by
    have h₁ : GeometricallyConnected ((Over.forget _).map (snd (splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
        (GlobalTheory.Diag.geometricallyConnected_hom S X)
    have h₂ : Surjective ((Over.forget _).map Q.q) := Q.q_surj
    exact @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ sq h₂ h₁
  rw [← Over.w Q.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

variable {Y Y' : Scheme.{0}} {L : LB Y} {L' : LB Y'} {F : Y' ⟶ Y}

theorem exists_iso_ratio (hL : L.IsLB) (hL' : L'.IsLB) {w₁ w₂ : LB.Iso L' (L.pull F)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) (j : L.ι) (k : L'.ι), F (r y) ∈ L.U j → r y ∈ L'.U k →
      gw w₁ r y j k = gm r y ⊤ u * gw w₂ r y j k := by
  have h₁ := (isGen_iff _).1 g₁
  have h₂ := (isGen_iff _).1 g₂
  let W : L.ι × L'.ι → Y'.Opens := fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2
  let v : ∀ p, Γ(Y', W p)ˣ := fun p => w₁.s (fun _ => p.1, p.2) * (w₂.s (fun _ => p.1, p.2))⁻¹
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) p, gm r y (W p) (v p) =
      gw w₁ r y p.1 p.2 * (gw w₂ r y p.1 p.2)⁻¹ := fun Z r y p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩) v (fun p q x hx => by
      have a := h₁ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      rw [hv, hv, a, b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r y j k hj hk => ?_⟩
  have hy : r y ∈ W (j, k) := ⟨mem_pull.2 hj, hk⟩
  rw [← gm_res r y (le_top : W (j, k) ≤ ⊤) hy u, hu, hv, inv_mul_cancel_right]

end General

section Invariant
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem act_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) (x : T ⟶ G) :
    ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := by
  have := Q.q_hom
  rw [← Over.comp_left, MonObj.mul_comp, Q.comp_i_q, _root_.one_mul, Over.comp_left]

end Invariant

end GlobalTheory.TrivDescentCompare
end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ZM.Model
open Out.Inh

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {k : ℕ}

theorem lbIso_of_g {X : Scheme.{0}} (L M : LB X) (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have h : (LB.div M L).g i j = 1 :=
    (congrArg₂ (· * ·) ((congrArg _ (hM _ _)).trans (map_one _)) ((congrArg (·⁻¹) ((congrArg _ (hL _ _)).trans
      (map_one _))).trans inv_one)).trans (_root_.mul_one _)
  exact (map_one _).trans ((congrArg₂ (· * ·) h (map_one _)).trans (_root_.mul_one _)).symm

theorem isIso_of_dim_zero (A : Over S) [GrpObj A] (h : IsAbelianScheme A) (hd : SmoothOfRelativeDimension 0 A.hom) :
    IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) := ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem lbIso_of_gen {X : Scheme.{0}} (L M : LB X) (F : X ⟶ X) (hF : F = 𝟙 X) (t : LB.Gen (L.pull F)) (ht : t.IsGen)
    (hM : ∀ i j, M.g i j = 1) : LBIso L M := by
  subst hF
  have le : ∀ p : M.ι × L.ι, M.U p.1 ⊓ L.U p.2 ≤ (L.pull (𝟙 X)).U (fun _ => p.2) :=
    fun p y hy => Set.mem_iInter.2 fun _ => hy.2
  refine ⟨⟨fun p => (res (le p) (t.s fun _ => p.2))⁻¹⟩, fun p q => ?_⟩
  have hle : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤
      (L.pull (𝟙 X)).U (fun _ => p.2) ⊓ (L.pull (𝟙 X)).U (fun _ => q.2) := inf_le_inf (le p) (le q)
  have key := congrArg (res hle) (ht (fun _ => p.2) (fun _ => q.2))
  erw [map_mul, DVR.res_res', DVR.res_res'] at key
  have aux : ∀ {G : Type} [CommGroup G] (a g b a' m g' b' : G), a = g * b → a' = a⁻¹ → m = 1 → g' = g → b' = b⁻¹ →
      a' = m * g'⁻¹ * b' := by
    rintro G _ a g b a' m g' b' rfl rfl rfl rfl rfl
    rw [_root_.one_mul, mul_inv]
  refine aux _ _ _ _ _ _ _ key ((map_inv _ _).trans (congrArg _ (DVR.res_res' _ _ _)))
    ((congrArg _ (hM _ _)).trans (map_one _)) ?_ ((map_inv _ _).trans (congrArg _ (DVR.res_res' _ _ _)))
  dsimp only [LB.pull, LB.LinComb]
  erw [Fintype.prod_unique, zpow_one, DVR.res_res']
  rfl

theorem linComb_g_one {X Y : Scheme.{0}} (M : LB X) (hg : ∀ i j, M.g i j = 1) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : (LB.LinComb M φ ε).ι) : (LB.LinComb M φ ε).g j j' = 1 :=
  Finset.prod_eq_one fun _ _ => by rw [hg, map_one]; erw [map_one]; exact one_zpow _

end GlobalTheory.ZM.Model
end

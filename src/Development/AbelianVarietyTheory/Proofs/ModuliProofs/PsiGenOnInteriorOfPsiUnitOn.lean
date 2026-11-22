import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PsiUnitOnIffInterior
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegActCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Type} [CommRing R] [IsDomain R]

section Act

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem gtAct_iff (oa : D.OAct O) (a : O) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ TorusGraphMaps.GtSmul oa a g g' := by
  have hG := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine and_congr Iff.rfl ?_
  have vu : ∀ {f f' : D.P.A ⟶ D.P.A} (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f f') rosatiε))
      {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun u y J hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  constructor
  · intro h
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨u₁, h₁, n₁⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    obtain ⟨u₂, h₂, n₂⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨u₂, ⟨h₂, n₂⟩, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have e := val_corr hJ (h u₁ h₁ n₁ χ) (𝟙 _)
    rw [val_mul hJ, vu u₁ hJ] at e
    rw [val_mul hJ, vu u₂ hJ, DVR.ros_swap hG D.P.isAb D.P.isLB _ _ u₁ h₁ n₁ u₂ h₂ n₂ hJ, ← e,
      mul_inv_cancel_right]
  · rintro ⟨u₂, ⟨h₂, n₂⟩, h⟩ u₁ h₁ n₁ χ
    refine corr_of_val D.P.isLB fun y J hJ => ?_
    have e := val_corr hJ (h χ) (𝟙 _)
    rw [val_mul hJ, vu u₂ hJ, DVR.ros_swap hG D.P.isAb D.P.isLB _ _ u₁ h₁ n₁ u₂ h₂ n₂ hJ] at e
    rw [val_mul hJ, vu u₁ hJ, ← e, inv_mul_cancel_right]

theorem qkAdd_iff {k : ℕ} (p p' p'' : QkPt D F k) :
    Geo.Tor.QkAdd p p' p'' ↔ TorusGraphMaps.QkAdd p p' p'' := Iff.rfl

theorem qkAct_iff (oa : D.OAct O) (a : O) {k : ℕ} (p p' : QkPt D F k) :
    QkAct oa a p p' ↔ TorusGraphMaps.QkSmul oa a p p' :=
  exists_congr fun q => and_congr Iff.rfl (and_congr (gtAct_iff oa a p.g q.g) Iff.rfl)

end Act

section Ext

variable {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] {k : ℕ}

theorem qkExt_unique {f : F →+* F'} {p : QkPt D F k} {q q' : QkPt D F' k} (h : QkExt f p q)
    (h' : QkExt f p q') : q = q' := by
  have hg : q.g = q'.g :=
    TorusExt.gt_ext_val (Over.OverMorphism.ext (h.2.1.trans h'.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (h.2.2 χ) _).trans (val_corr hJ (h'.2.2 χ) _).symm
  have hy : q.y = q'.y := h.1.trans h'.1.symm
  obtain ⟨y, g, e⟩ := q
  obtain ⟨y', g', e'⟩ := q'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

end Ext

section Through

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]

abbrev rigVal (D : DegPre R) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r z J

theorem prod_graph (f : D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i, h (TorusGraphMaps.graphφ D.P.A f i) ^ TorusGraphMaps.graphε i =
      h (padd D.P.A (𝟙 _) f).left * (h (𝟙 _))⁻¹ * (h f.left)⁻¹ * h (toUnit D.P.A ≫ η[D.P.A]).left * (h (𝟙 _))⁻¹ := by
  rw [Fin.prod_univ_five]
  show h (padd D.P.A (𝟙 _) f).left ^ (1 : ℤ) * h (𝟙 _) ^ (-1 : ℤ) * h f.left ^ (-1 : ℤ) *
    h (toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) * h (𝟙 _) ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_four (f : D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 4, h ((![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] :
        Fin 4 → _) i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      h (padd D.P.A (𝟙 _) f).left ^ (1 : ℤ) * h (𝟙 _) ^ (-2 : ℤ) * h f.left ^ (-1 : ℤ) *
        h (toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) := by
  rw [Fin.prod_univ_four]; rfl

end Through

section Unit

variable (D : DegPre R) (χ : D.X)

theorem generic_le (j : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hV hy

end Unit

end GlobalTheory.DegActCompare

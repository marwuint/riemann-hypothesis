import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LieArcSt
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LieLiftsTangentReduction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps

noncomputable section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  have hF : ∀ χ, FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim
      (DegPre.gtφT D T 1 χ) DegPre.gtε := fun χ U _ h => by
    have := prod_Oφ_zero (D := D) (1 : T ⟶ D.P.A) (𝟙 _) T.hom (by
      show 𝟙 _ ≫ (toUnit T ≫ η[D.P.A]).left = _
      simp [eSec]) χ h
    simp only [Category.id_comp] at this
    rw [TorusCoord.gtφT_eq]
    exact (Fintype.prod_empty _).trans this.symm
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (LB.oneGen D.P.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  have v1 : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = 1 := fun χ y J hJ =>
    (vs χ _ _ y J hJ).trans (val_one _)
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  have c := val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1
  rw [MonObj.comp_one, (isCub_cubV D.cub hJ).face₃] at c
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) c)).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) (v1 _ y J hJ))).symm

variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.ArcLieCompare

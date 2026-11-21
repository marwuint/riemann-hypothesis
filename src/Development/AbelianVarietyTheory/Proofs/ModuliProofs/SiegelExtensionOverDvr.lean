import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaExtend

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.ThetaObjPull

theorem pic_local {R : Type} [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨U, hU, h⟩ := locZero_base (𝟙 (Sp R)) c (IsLocalRing.closedPoint R)
  have := pull_eq_zero_of_range h (𝟙 _) fun y =>
    (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hU
  rwa [pull_id, pull_id] at this

theorem locZero_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (h₁ : LocZero (fst T A).left (cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _))) :
    LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have h₂ := (h₁.sub (locZero_base (fst T A).left (pull x.left (cls L hL)))).sub
    (locZero_base (fst T A).left (-pull (1 : T ⟶ A).left (cls L hL)))
  convert h₂ using 1
  rw [cls_translDiff hL, lam]
  simp only [map_neg, ← pull_comp, ← Over.comp_left, MonObj.comp_one]
  abel

theorem kTriv_of_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (e : cls P hP = lam (cls L hL) (fst A A) (snd A A))
    (h : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv A L := by
  intro R _ t x hx
  have h₁ := (locZero_iff _ (LB.isLB_linComb hL _ _)).1 hx
  have h₂ := locZero_lam hL x h₁
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨V, hV, H⟩ := h₂ p
  refine ⟨V, hV, ?_⟩
  let T' : Over S := Out.overRes (T := Over.mk t) V
  let i : T' ⟶ Over.mk t := Out.overResι V
  have H' := pull_eq_zero_of_range H (lift (snd A T' ≫ i) (fst A T')).left fun y => by
    have e := congrArg (fun q => q.left y) (lift_fst (snd A T' ≫ i) (fst A T'))
    show (fst (Over.mk t) A).left ((lift (snd A T' ≫ i) (fst A T')).left y) ∈ V
    refine e ▸ ?_
    exact ((snd A T').left y).2
  have := h T' (i ≫ x) ((cls_eq_zero_iff (pull_isLB hP _)).1 (by
    rw [cls_pull hP, e, pull_lam, lift_fst, lift_snd]
    rwa [pull_lam, lift_fst_assoc, lift_snd, Category.assoc] at H'))
  exact congrArg (fun q => q.left) (this.trans (MonObj.comp_one i).symm)

end GlobalTheory.ThetaExtend

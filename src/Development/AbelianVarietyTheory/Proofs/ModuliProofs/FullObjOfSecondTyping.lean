import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FullLevelModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaOfPushInvertible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Models GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel

noncomputable section

namespace GlobalTheory.ModelTypings

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H}

def fullPull {N : ℕ} {B : Type} [CommRing B] {ρ ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N ρ ζ s) {f : S' ⟶ S} {t' : SAB H S'} (m : SABMap t' o.t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hlv : ∀ a, (lv a).left ≫ m.φ = f ≫ (o.lev a).left) {s' : S' ⟶ Sp B}
    (hs : f ≫ s = s') : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N ρ ζ s' :=
  have hlv' : ∀ a, lv a = GlobalTheory.ObjPull.secPull m.cart (o.lev a) := fun a => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · exact (hlv a).trans (GlobalTheory.ObjPull.secPull_left m.cart _).symm
    · rw [Over.w, Over.w]
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    lev := lv
    lev_add := fun a c => by rw [hlv', hlv', hlv', o.lev_add, map_mul]
    lev_lin := fun c a => by
      apply Over.OverMorphism.ext
      apply m.cart.1.hom_ext
      · refine (hlv _).trans ?_
        rw [o.lev_lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ _) (hlv a).symm
      · rw [Over.w, Over.w]
    lev_ker := fun a => by rw [hlv', o.lev_ker a, map_one]
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨h₁, h₂, h₃⟩ := o.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
      obtain ⟨e, he⟩ := LevelFibre.exists_ptEquiv m.cart x _ rfl
      have hl : ∀ a, e (toUnit _ ≫ lv a) = toUnit _ ≫ o.lev a := fun a => by
        apply Over.OverMorphism.ext
        rw [he, LevelFibre.unit_left, LevelFibre.unit_left, Category.assoc, Category.assoc]
        exact congrArg _ (hlv a)
      refine ⟨fun a => by rw [← h₁, ← hl, map_eq_one_iff e e.injective], fun g hg => ?_, fun a b => ?_⟩
      · obtain ⟨a, ha⟩ := h₂ (e g) (by rw [← map_pow, hg, map_one])
        exact ⟨a, e.injective ((hl a).trans ha)⟩
      · refine (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ o.t.PP.isLB t'.PP.isLB m.cart hL
          (Over.mk x) N _ _ (e _) (e _) _ (he _) (he _)).2 ?_
        rw [hl, hl]
        exact h₃ a b
    geom0 := fun k _ _ _ x β hx =>
      (FamAut.geomAt_iff m hlv x _ _).2 (o.geom0 k (x ≫ f) β (by rw [Category.assoc, hs, hx])) }

abbrev inc (H : Host E) (S A : ℕ) : RZ H S A →+* oRing H A S := Subring.inclusion (RZ_eq H S A).le

abbrev inc' (H : Host E) (S A : ℕ) : oRing H A S →+* RZ H S A := Subring.inclusion (RZ_eq H S A).symm.le

instance (S A : ℕ) : IsIso (spMap (inc H S A)) := isIso_incl (RZ_eq H S A)

instance (S A : ℕ) : IsIso (spMap (inc' H S A)) := isIso_incl (RZ_eq H S A).symm

def SiegelClauseFullLevel {N n : ℕ} {XX : Scheme.{0}} (w : XX ⟶ Sp (oRing H N n))
    (oX : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) w) : Prop :=
  ∀ (p : ℕ) (hn : n.Coprime p), p.Prime →
    ∃ (Ag : SiegelFamily (gDim D) p N) (bas : (Fin (gDim D) ⊕ Fin (gDim D) → ℤ) ≃ₗ[ℤ] D.La)
      (cl : pullback w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ⟶
        pullback Ag.s (spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
      (o : SiegPre (gDim D) N (zetaZP p N)
        (pullback.snd w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ≫
          spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
      (φ : o.A.left ⟶ oX.t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 oX.t.G).left),
      (∀ a b, D.EF (bas a) (bas b) = omegaStd a b) ∧
      IsGrpPullback o.A oX.t.G (pullback.fst _ _) φ ∧ IsSquare φ φ₂ ∧
      LBIso o.P ((abelian₂ oX.t.G oX.t.PP.L).pull φ₂) ∧
      (∀ a, (o.lev a).left ≫ φ = pullback.fst _ _ ≫ (oX.lev (bas a)).left) ∧
      cl ≫ pullback.snd _ _ = pullback.snd _ _ ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧
      IsFinite cl ∧ FormallyUnramified cl

structure Fam {N n : ℕ} (Z : FullPre D N n) where
  XX : Scheme.{0}
  w : XX ⟶ Sp (oRing H N n)
  oX : IndefiniteRowSideFullHecke.FullLevelModel.FullObj D N (oRt H N n) (oZeta H N n) w
  u : Z.U.toScheme ⟶ XX
  fm : FullMap Z.ab oX u
  W : XX.Opens
  red : IsReduced XX
  flat : Flat w
  overB : u ≫ w = Z.U.ι ≫ Z.s
  fin : IsFinite u
  surj : Surjective u
  iso : IsIso (u ∣_ W)
  gen : ∀ x : XX, CharZero (XX.residueField x) → x ∈ W
  sieg : SiegelClauseFullLevel w oX

theorem incl_incl_apply {R R' : Subring ℂ} (h : R ≤ R') (h' : R' ≤ R) (x : R') :
    Subring.inclusion h (Subring.inclusion h' x) = x := rfl

variable {Xo : ∀ l : Level H, Moduli D l} {n J : ℕ}

end GlobalTheory.ModelTypings

end

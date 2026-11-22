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

variable {Xo : ∀ l : Level H, Moduli D l} {n J : ℕ}

end GlobalTheory.ModelTypings

end

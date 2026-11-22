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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Models GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel

noncomputable section

namespace GlobalTheory.ModelTypings

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ_eq (H : Host E) (S A : ℕ) : RZ H S A = oRing H A S := by
  unfold RZ oRing w0C
  rw [Set.pair_comm]

theorem incl_self {R : Subring ℂ} (h : R ≤ R) : spMap (Subring.inclusion h) = 𝟙 _ := Spec.map_id _

theorem isIso_incl {R R' : Subring ℂ} (h : R = R') : IsIso (spMap (Subring.inclusion h.le)) := by
  subst h
  rw [incl_self]
  infer_instance

section Rebase

variable {U : Scheme.{0}} {F : Type} [Field F] {c : U ⟶ Sp F} {t₀ : SAB H U} {R R' : Subring ℂ}
  {β : R →+* F} {β' : R' →+* F}

def genIso (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    pullback s (spMap β') ⟶ pullback (s ≫ spMap (Subring.inclusion h.le)) (spMap β) :=
  pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (spMap (Subring.inclusion h.le)) (Category.id_comp _).symm
    (by rw [Category.id_comp, ← spMap_comp, hβ])

instance (h : R = R') (hβ : β'.comp (Subring.inclusion h.le) = β) {X : Scheme.{0}} (s : X ⟶ Sp R') :
    IsIso (genIso h hβ s) := by
  have := isIso_incl h
  unfold genIso
  infer_instance

end Rebase

end GlobalTheory.ModelTypings

end

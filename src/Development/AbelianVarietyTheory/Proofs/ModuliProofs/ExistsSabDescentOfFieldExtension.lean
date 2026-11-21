import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LevelActionTransitions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Action

open IndefiniteRowSideFullHecke.LevelActionTransitions (KMax Sends FixesLevel modulus cls exists_sends)

variable (Y : Model Xo c β)

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have h := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance
  ⟨h.1, h.2.2⟩

theorem comp_over {r : Xo.XF c ⟶ Xo.XF c} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _) :
    r ≫ pullback.fst _ _ ≫ Xo.s = pullback.fst _ _ ≫ Xo.s := by
  rw [pullback.condition, ← Category.assoc, hr]

theorem move_unique {r r' : Xo.XF c ⟶ Xo.XF c} (ν : SABMap Y.oF.t Y.oF.t r) (ν' : SABMap Y.oF.t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = pullback.snd _ _) (hr' : r' ≫ pullback.snd _ _ = pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) :
    r = r' ∧ ν.φ = ν'.φ := by
  let o := objOfSABMap Y.oF ν
  have e₁ : ∀ a, (o.eta a).left ≫ ν.φ = r ≫ (Y.oF.eta a).left := (objMapOfSABMap Y.oF ν).eta
  have e₂ : ∀ a, (o.etaA a).left ≫ ν.φ = r ≫ (Y.oF.etaA a).left := (objMapOfSABMap Y.oF ν).etaA
  have e₁' : ∀ a, (o.eta a).left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left := fun a => by
    obtain ⟨x, h, h'⟩ := hM a
    obtain rfl := sec_eq_secPull ν h
    exact h'
  have e₂' : ∀ a, (o.etaA a).left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left := fun a => by
    obtain ⟨x, h, h'⟩ := hA a
    obtain rfl := sec_eq_secPull ν h
    exact h'
  have key : ∀ {q : Xo.XF c ⟶ Xo.XF c} (n : SABMap o.t Y.oF.t q), (∀ a, (o.eta a).left ≫ n.φ = q ≫ (Y.oF.eta a).left) →
      (∀ a, (o.etaA a).left ≫ n.φ = q ≫ (Y.oF.etaA a).left) → Nonempty (ObjMap o Xo.univ (q ≫ pullback.fst _ _)) :=
    fun n h₁ h₂ => (ObjComp.objMap_comp Y.m0 (⟨n, h₁, h₂⟩ : ObjMap o Y.oF _)).nonempty
  have hf : r ≫ pullback.fst _ _ = r' ≫ pullback.fst _ _ :=
    (Xo.rep _ _ (isReduced_XF Xo c).1 o).unique ⟨Category.assoc _ _ _, key ν e₁ e₂⟩
      ⟨by rw [Category.assoc, comp_over hr', comp_over hr], key ν' e₁' e₂'⟩
  obtain rfl : r = r' := pullback.hom_ext hf (hr.trans hr'.symm)
  exact ⟨rfl, obj_rigid_closed abelianSchemeLaws_all.1 E H D l _ _ _ _ _ _ _ _ Y.oF o r (Or.inl (isReduced_XF Xo c).1)
    ν ν' fun a => ⟨_, e₁ a, e₁' a⟩⟩

def Moves (k : KMax D) (r : Xo.XF c ⟶ Xo.XF c) (ν : SABMap Y.oF.t Y.oF.t r) : Prop :=
  r ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ a b, Sends l k a b →
    (Y.oF.eta b).left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ (Y.oF.etaA b).left ≫ ν.φ = r ≫ (Y.oF.etaA a).left

variable {Y}

theorem Moves.unique {k : KMax D} {r r' : Xo.XF c ⟶ Xo.XF c} {ν : SABMap Y.oF.t Y.oF.t r}
    {ν' : SABMap Y.oF.t Y.oF.t r'} (h : Moves Y k r ν) (h' : Moves Y k r' ν') : r = r' ∧ ν.φ = ν'.φ :=
  move_unique Y ν ν' h.1 h'.1
    (fun a => (exists_sends l k a).elim fun b hb => ⟨_, (h.2 a b hb).1, (h'.2 a b hb).1⟩)
    (fun a => (exists_sends l k a).elim fun b hb => ⟨_, (h.2 a b hb).2, (h'.2 a b hb).2⟩)

variable (Y)

end Action

end GlobalTheory.ModelRelCompare

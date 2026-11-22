import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) :
    (onAff A hV').left ⟶ (onAff A hV).left :=
  pullback.lift (pullback.fst A.hom hV'.fromSpec)
    (pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op))
    (by rw [pullback.condition, Category.assoc, hV.map_fromSpec hV' (homOfLE h).op])

@[reassoc (attr := simp)] theorem bcProj_fst {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem bcProj_snd {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.snd A.hom hV.fromSpec =
      pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op) :=
  pullback.lift_snd _ _ _

section Data

variable {A} (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
  (hg : SmoothOfRelativeDimension g A.hom)

include hA in
theorem isAbelianScheme_onAff {V : T.Opens} (hV : IsAffineOpen V) : IsAbelianScheme (onAff A hV) :=
  isAbelianScheme_pullback_obj hV.fromSpec A hA

include hg in
theorem smooth_onAff {V : T.Opens} (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension g (onAff A hV).hom :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback A.hom hV.fromSpec) hg

include H hA hg in
theorem small_primDR {V : T.Opens} (hV : IsAffineOpen V) : Small.{0} (primDR (onAff A hV)) := by
  obtain ⟨hf, -, -⟩ := H.1.prim (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Γ(T, V) (primDR (onAff A hV))
  exact small_of_surjective hf

def modV {V : T.Opens} (hV : IsAffineOpen V) : Type :=
  @Shrink.{0} (primDR (onAff A hV)) (small_primDR H hA hg hV)

instance {V : T.Opens} (hV : IsAffineOpen V) : AddCommGroup (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

instance {V : T.Opens} (hV : IsAffineOpen V) : Module Γ(T, V) (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

end Data

end GlobalTheory.DeRhamSheaf

namespace GlobalTheory.AffGlue

end GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

end GlobalTheory.DeRhamSheaf

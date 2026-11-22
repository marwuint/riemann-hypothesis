import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf.VB

open GlobalTheory.Published.AbelianDeRham (bcMor)

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

theorem fromSpec_res {U W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    letI := resAlg h
    spMap (algebraMap Γ(T, U) Γ(T, W)) ≫ hU.fromSpec = hW.fromSpec :=
  hU.map_fromSpec hW (homOfLE h).op

theorem isGrpPullback_congr {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f₁ f₂ : S' ⟶ S} {φ : G'.left ⟶ G.left} (e : f₁ = f₂) (h : IsGrpPullback G' G f₁ φ) :
    IsGrpPullback G' G f₂ φ := e ▸ h

theorem isAbelianScheme_onAff (hA : IsAbelianScheme A) {V : T.Opens} (hV : IsAffineOpen V) :
    IsAbelianScheme (onAff A hV) :=
  GlobalTheory.isAbelianScheme_pullback_obj _ A hA

theorem smooth_onAff {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom) {V : T.Opens}
    (hV : IsAffineOpen V) : SmoothOfRelativeDimension g (onAff A hV).hom := by
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
    (isGrpPullback_pullback A hV.fromSpec).1 hg

theorem exists_transition {U W : T.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    letI := resAlg h
    ∃ φ : (onAff A hW).left ⟶ (onAff A hU).left,
      IsGrpPullback (onAff A hW) (onAff A hU) (spMap (algebraMap Γ(T, U) Γ(T, W))) φ ∧
      φ ≫ pullback.fst A.hom hU.fromSpec = pullback.fst A.hom hW.fromSpec :=
  letI := resAlg h
  ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (G'' := onAff A hW) hU.fromSpec _
    (isGrpPullback_congr (G' := onAff A hW) (fromSpec_res hU hW h).symm
      (isGrpPullback_pullback A hW.fromSpec)),
    pullback.lift_fst _ _ _⟩

end GlobalTheory.DeRhamSheaf.VB

namespace GlobalTheory.DeRhamSheaf.VB

end GlobalTheory.DeRhamSheaf.VB

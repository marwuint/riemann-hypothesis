import Mathlib
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

end GlobalTheory.StalkJet

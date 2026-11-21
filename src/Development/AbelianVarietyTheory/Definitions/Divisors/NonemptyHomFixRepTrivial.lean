import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}}

structure HomFixRep (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grpA : GrpObj AH]
  BH : Over H
  [grpB : GrpObj BH]
  φA : AH.left ⟶ A.left
  φB : BH.left ⟶ B.left
  pbA : IsGrpPullback AH A π φA
  pbB : IsGrpPullback BH B π φB
  Φ : AH ⟶ BH
  hom : IsMonHom Φ
  iso : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
      IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

attribute [instance] HomFixRep.grpA HomFixRep.grpB

theorem isGrpPullback_id (A : Over S) [GrpObj A] : IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 _) (by simp)
  have h1 : e ≫ x₀ = x := by ext; simp [e, hx]
  have h2 : e ≫ y₀ = y := by ext; simp [e, hy]
  have h3 : e ≫ (x₀ * y₀) = x * y := by rw [MonObj.comp_mul, h1, h2]
  rw [← h3]; simp [e]

end GlobalTheory.EndLoc

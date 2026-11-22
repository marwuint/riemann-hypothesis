import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open GlobalTheory.ArchMetricCompare (cj cjPt_comp val_cj)
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} (w : φ ≫ A.hom = A'.hom ≫ f)
    (w' : ψ ≫ A'.hom = A''.hom ≫ g) (w'' : (ψ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) :
    sqMap w'' = sqMap w' ≫ sqMap w :=
  (pullback.map_comp ψ φ ψ φ g f w'.symm w'.symm w.symm w.symm).symm

namespace PPAS.RiemannData

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

def conj : P.RiemannData (spMap (starRingEnd ℂ) ≫ y) :=
  have h := isGrpPullback_pullback d.B cj
  have hL := pull_isLB d.isLB (pullback.fst d.B.hom cj)
  { B := (Over.pullback cj).obj d.B
    φ := pullback.fst d.B.hom cj ≫ d.φ
    isPull := h.comp d.isPull
    L := d.L.pull (pullback.fst d.B.hom cj)
    isLB := hL
    pol := by
      rw [sqMap_comp d.isPull.1.w h.1.w, CechPic.pull_comp, d.pol]
      exact (pull_sqMap_lam h _).trans
        (congrArg (CechPic.lam · _ _) (CechPic.cls_pull d.isLB _ hL).symm)
    u := ConjUnif.conjPull h d.u
    H := d.H.map star
    χ := _
    isAH := ConjUnif.conjPull_isAH h d.u d.isAH }

theorem conj_H : d.conj.H = d.H.map star := rfl

end PPAS.RiemannData

end GlobalTheory

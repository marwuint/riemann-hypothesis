import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Elliptic

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

variable {A}

theorem cls_pull_lam {L : LB A.left} (hL : L.IsLB) {T : Over S} (x y : T ⟶ A)
    (h : ((abelian₂ A L).pull (lift x y).left).IsLB) : cls _ h = lam (cls L hL) x y := by
  rw [cls_pull (L := abelian₂ A L) (LB.isLB_linComb hL _ _) _ h]
  erw [cls_cube_two hL (fst A A) (snd A A)]
  rw [pull_lam, lift_fst, lift_snd]

end

variable {k : Type} [Field k] [IsAlgClosed k] (Q : Out.PolAV (Sp k)) (hg : Q.g = 1)

end GlobalTheory.RealMult.Elliptic

namespace GlobalTheory.RealMult

end GlobalTheory.RealMult

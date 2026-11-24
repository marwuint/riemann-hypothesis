module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section
namespace GlobalTheory.CubeThm

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem comp_psum {T T' : Over S} {n : ℕ} (f : T' ⟶ T) (v : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    f ≫ psum B v I = psum B (fun i => f ≫ v i) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

theorem lift_comp_cubeCoordinates (x y z : B ⟶ B) :
    (fun i => lift x (lift y z) ≫ x3 B i) = ![x, y, z] := by
  funext i
  fin_cases i <;> simp [x3]

theorem cube_pic (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB
  have hT : (Theta B M.L.L).IsLB := LB.isLB_linComb M.L.isLB _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1

  rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  norm_num at h2
  rw [← sub_eq_zero, ← h2]
  abel

end GlobalTheory.CubeThm

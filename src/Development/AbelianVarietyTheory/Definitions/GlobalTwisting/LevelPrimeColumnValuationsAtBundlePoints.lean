import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.AllBundlePointProperties

open GlobalTheory.Fc

def LevelPrimeColumnValuationsClosed (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u

def LevelPrimeColumnValuationsAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => LevelPrimeColumnValuationsClosed 𝒜

def H_aAtG (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

def ArithmeticConditionAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aAtG 𝒜

structure All (𝒜 : FamClass) : Prop where
  aP10 : LevelPrimeColumnValuationsClosed 𝒜
  aAtG : H_aAtG 𝒜

end GlobalTheory.Fc.AllBundlePointProperties

end

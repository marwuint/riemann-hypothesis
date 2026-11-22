import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

open GlobalTheory.Fc

def ReferenceChainEvaluationAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u

def ReferenceChainEvaluationAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ReferenceChainEvaluationAdmissible 𝒜

def H_aPtTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw

def TwistedPointAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPtTw 𝒜

def H_aPer0 (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)

def PeriodAtZeroAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPer0 𝒜

def H_aPerTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def TwistedPeriodAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPerTw 𝒜

def H_tie (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.RealPlaceSecondLayerConditions Fm

def Row_tie {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_tie 𝒜

structure All (𝒜 : FamClass) : Prop where
  aPt0 : ReferenceChainEvaluationAdmissible 𝒜
  aPtTw : H_aPtTw 𝒜
  aPer0 : H_aPer0 𝒜
  aPerTw : H_aPerTw 𝒜
  tie : H_tie 𝒜

end GlobalTheory.Fc.PeriodEntriesOverColumns

end

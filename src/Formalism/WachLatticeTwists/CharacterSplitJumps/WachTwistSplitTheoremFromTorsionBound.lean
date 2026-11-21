import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremStatedForm

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JS

def HZeroHypothesesJumps {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (J : Multiset ℤ) : Prop :=
  (-1 : ℤ) ∉ J ∧ J ≠ 0 ∧ 1 ≤ m ∧ (ℓ = 2 → 2 ≤ m) ∧ PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m ∧
  D.piece.Inputs w (jumpsDualTwist J) 0 ∧ D.Union ∧ D.Flat ∧ D.LES ∧ D.Inv

end Formalism.RepresentationBoundsCohomology.JT

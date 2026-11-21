import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty

noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

end GlobalTheory.LvT.PendExample

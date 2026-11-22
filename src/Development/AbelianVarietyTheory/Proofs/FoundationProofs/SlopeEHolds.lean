import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeSumWeylAndDualWeylLatticesLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeDualSumWeylLatticesLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefGramSelfDualAfterFieldEmbedding

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem slopeK_holds : SlopeK := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hs G hG C _ M hM N e X
  exact ⟨_root_.GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK K v₀ hv ι n lam R hR hs G hG C M hM N e X,
    _root_.GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK K v₀ hv ι n lam R hR hs G hG C M hM N e X⟩

theorem slopeE_holds : SlopeE := by
  intro E K _ _ _ _ _ _ v₀ hv cE hcE ι _ emb hemb n lam R hR hs J hJ C _ L hL N e X
  have h := _root_.GlobalTheory.TestLat.defGram_selfDual_of_embedding E K cE hcE ι emb hemb n J hJ
  have h1 := slopeK_holds K v₀ hv ι n lam R hR hs (gramK emb J) (fun τ => (h τ).1) C
    (fun c τ => tauLat emb τ (L c)) (fun c τ => ((h τ).2.2 (L c) (hL c)).1) N e X
  have h2 := slopeK_holds K v₀ hv ι n lam R hR hs (gramKd emb J) (fun τ => (h τ).2.1) C
    (fun c τ => dualFr (tauLat emb τ (L c))) (fun c τ => ((h τ).2.2 (L c) (hL c)).2) N e X
  exact ⟨h1.2, fun hm => (h1.1 hm).1, h2.2, fun hm => (h2.1 hm).1⟩

theorem slope_holds : GlobalTheory.TestLat.SlopeK ∧ GlobalTheory.TestLat.SlopeE := ⟨slopeK_holds, slopeE_holds⟩

end GlobalTheory.TestLat

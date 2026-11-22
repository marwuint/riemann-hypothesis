import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.NotAboveTransGenSelf
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtPOfFineUniq
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsOrderfree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k)

include hZ hI in
theorem standardCosocle_of : GlobalTheory.Published.StandardCosocleGL := by
  have hA := irreducibleAdmissibleGL
  intro k _ _ _ _ _ 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := _root_.GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual hA (_root_.GlobalTheory.CompanionTheory.SegLDual.lSegDual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := _root_.GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) (hI k) (_root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k hA (hI k)) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact _root_.GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr x hd) (isSmooth_prodIrr x hd) (_root_.GlobalTheory.CompanionTheory.ProdFL.main hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

include hI in
theorem lOrderFree_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LOrderFree k :=
  PositivityTheory.PfEss.Zc2.cs_orderfree irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (hI k))

include hI in
theorem lSocleGL_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LSocleGL k :=
  _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal irreducibleAdmissibleGL) (lOrderFree_of hI k)

include hZ hI in
theorem exhaustion_of_three (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], MidP k ∧ RefineP k ∧ SwapP k) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hA := irreducibleAdmissibleGL
  refine exhaustion_of_steps fun k _ _ _ _ _ => ?_
  obtain ⟨hM, hR, hS⟩ := H k
  have hC := cuspEmbP_of_refine k hR
  exact ⟨hM, hR, hS, hC, suppP k, juxtP_of_fineUniq hA hM hR hS hC (GlobalTheory.T.segment_product_word_in_shuffle hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)) (_root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ),
    linkP, minP, peelGoodP (standardCosocle_of hZ hI) (lSocleGL_of hI k) hR⟩

include hZ hI in
theorem multisegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments :=
  GlobalTheory.T.langlands_multisegments_of_exhaustion_gl irreducibleAdmissibleGL (lSocleGL_of hI) (fun _ _ _ _ _ => _root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet irreducibleAdmissibleGL hZ) (lOrderFree_of hI) hE

end PositivityTheory.Exh

end

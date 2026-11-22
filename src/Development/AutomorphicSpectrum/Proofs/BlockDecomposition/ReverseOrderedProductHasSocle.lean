import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleRev

theorem exists_isSocle_prodIrr_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k →
    LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N),
    IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  intro k _ _ _ _ hA hJ hI hC h N Γ y hd hR hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order Γ
  have hR' : IsRevOrdered (Γ ∘ σ) := _root_.GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon _ hσ
  have hd' : ∑ a, (y (σ a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp σ (fun a => (y a).1)
  obtain ⟨e₁⟩ := _root_.GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered hA hC Γ σ y hd hd' hR hR' hL
  have hL' : ∀ i, IsLSeg ((Γ ∘ σ) i) ((y ∘ σ) i).rep := fun i => hL (σ i)
  obtain ⟨g, z, hz, ⟨e₂⟩, hjm⟩ := _root_.GlobalTheory.CompanionTheory.GroupCount.groupCount hA hJ hI (Γ ∘ σ) (y ∘ σ) hd' hσ hL'
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA z hz hjm
  exact ⟨τ, hτ.of_equiv (Representation.Equiv.refl _) (e₁.trans e₂).symm⟩

end GlobalTheory.CompanionTheory.SocleRev

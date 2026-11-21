import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotientAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_swap_product_generic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  exact @GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap

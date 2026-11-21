import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.ProdReorder
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdjQuot

section Linear

theorem nontrivial_piTensorProduct {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push_neg at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

end Linear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Induction

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W W' : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    [Nontrivial W] : Nontrivial (IndSp e ρ) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

end Induction

theorem nontrivial_prodIrr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := by
  haveI : ∀ a, Nontrivial (x a).2.rep.V := fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (x a).2.rep.irr
  haveI := nontrivial_piTensorProduct (X := fun a => (x a).2.rep.V)
  exact nontrivial_indSp _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)

end GlobalTheory.CompanionTheory.AdjQuot
end

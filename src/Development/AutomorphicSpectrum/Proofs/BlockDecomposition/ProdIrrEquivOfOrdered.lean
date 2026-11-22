import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.SplitRead GlobalTheory.ProdReorder

noncomputable section

namespace GlobalTheory.CompanionTheory.SegReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem famCongr {u : ℕ} {f g : Fin u → IrrGL k} (hfg : ∀ i, f i = g i) {T : ℕ}
    (e : (Σ i, Fin (f i).1) ≃ Fin T) (e' : (Σ i, Fin (g i).1) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (f i).rep).Equiv (multiProd e' fun i => (g i).rep)) := by
  obtain rfl : f = g := funext hfg
  exact multiProd_placing e e' _

end GlobalTheory.CompanionTheory.SegReorder

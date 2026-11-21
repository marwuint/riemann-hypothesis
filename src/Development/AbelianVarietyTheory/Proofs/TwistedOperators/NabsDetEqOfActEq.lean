import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfPowerSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IdealChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_monLat {n : Type} {c : ℕ} {L : Submodule 𝒪[k] (n → k)} {b : ℕ → kˣ} {v : n ⊕ Fin c → k} :
    v ∈ monLat c L b ↔ (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, v (Sum.inr i) ∈ idl (b (i.val + 1)) := Iff.rfl

end GlobalTheory.IdealChain

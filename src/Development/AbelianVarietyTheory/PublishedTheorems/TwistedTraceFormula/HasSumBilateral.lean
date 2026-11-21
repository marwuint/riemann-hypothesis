import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG GlobalTheory.GLDoubling
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_haar (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] :
    ∃ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure ∧ μ (KO k (Fin n)) = 1 := by
  have ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isOpen_KO
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isCompact_KO
  let K : TopologicalSpace.PositiveCompacts (GL (Fin n) k) := ⟨⟨_, hc⟩, by
    rw [show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.GLDoubling.Model

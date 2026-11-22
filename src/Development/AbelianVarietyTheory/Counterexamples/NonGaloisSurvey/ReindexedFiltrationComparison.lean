import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

noncomputable section

namespace GlobalTheory.Survey.SlowDecayFunctions

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

variable {l : ℕ} [Fact l.Prime]

theorem continuous_cyc (P : LocPrime l) (K LL : FinExt l) :
    Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) := by
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

end GlobalTheory.Survey.SlowDecayFunctions

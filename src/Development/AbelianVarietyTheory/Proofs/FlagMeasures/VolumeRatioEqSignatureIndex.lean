import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsChoiceOfIdem

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩

end GlobalTheory.RowIndex

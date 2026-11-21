import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_unit_mem_open_archimedean_units : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty → ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  exact @GlobalTheory.UnitsDense.exists_unit_mem_open

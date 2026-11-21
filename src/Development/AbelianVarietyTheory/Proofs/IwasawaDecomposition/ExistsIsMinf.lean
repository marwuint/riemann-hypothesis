import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd _root_.GlobalTheory.CompactDualExists.nonempty_cdHaar

end GlobalTheory.MinfMeasure

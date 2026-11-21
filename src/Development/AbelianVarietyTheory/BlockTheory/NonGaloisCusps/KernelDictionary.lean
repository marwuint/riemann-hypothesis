import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RoundDown
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfKillsOne

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

variable {l : ℕ} [Fact l.Prime]

instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩

end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

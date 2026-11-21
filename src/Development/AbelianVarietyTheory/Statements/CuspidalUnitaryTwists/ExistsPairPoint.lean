import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Mass

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}

instance pointUnique (D : D7) (d : ℕ) : Unique (VC D 0 d) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

end GlobalTheory.NormSum.Mass

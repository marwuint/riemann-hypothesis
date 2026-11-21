import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers

section Lattices

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  Nat.card {w : HeightOneSpectrum (𝓞 E) // (p : 𝓞 E) ∈ w.asIdeal} = Module.finrank ℚ E

end Lattices

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers

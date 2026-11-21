import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Cls

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def FrOf {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

end Cls

end GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist

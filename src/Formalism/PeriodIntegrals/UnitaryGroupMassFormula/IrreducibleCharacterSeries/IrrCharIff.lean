import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

def ConjChar : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : FDRep ℂ G) (x : G), star (V.character x) = V.character x⁻¹

def IrrCharIff : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), IsIrrChar χ ↔ ∃ V : FDRep ℂ G, Simple V ∧ χ = V.character

end PI.SerBridgeGLW

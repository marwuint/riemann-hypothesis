import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

end Alg2

end PI.SelfDualHermitianLattices.Hd

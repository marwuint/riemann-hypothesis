import Formalism.PeriodIntegrals.HeisDefs

namespace PI

section Th

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def alG (s A : ℝ) (x : T → I → J → ℂ) : ℂ := (-1 : ℂ) ^ (round (s * (HfG A x x).re))

end Th

end PI

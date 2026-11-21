import Mathlib

noncomputable section

namespace PI.VolStabW

namespace FiniteFieldSplitting

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

end FiniteFieldSplitting

end PI.VolStabW

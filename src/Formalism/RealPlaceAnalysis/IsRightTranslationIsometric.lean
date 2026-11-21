import Formalism.RealPlaceAnalysis.SmoothOnGVIff

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.REAL

structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)

attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

end Formalism.REAL

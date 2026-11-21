import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
import Formalism.CharacterColumnKernels.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

structure Twist (ℓ : ℕ) [Fact ℓ.Prime] (E : Md ℓ) where

  HH : Md ℓ

  Wm : Md ℓ

  WX : Md ℓ

  gX : WX →ₗ[ℤ_[ℓ]] WX
  infm : Wm →ₗ[ℤ_[ℓ]] E
  infX : WX →ₗ[ℤ_[ℓ]] E
  res : E →ₗ[ℤ_[ℓ]] HH

namespace Twist

end Twist

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

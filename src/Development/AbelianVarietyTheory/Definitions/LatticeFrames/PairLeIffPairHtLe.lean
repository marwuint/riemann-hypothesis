import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

def Norming (B M : HLat K) (pr : B.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∀ (w : B.V) (v : InfinitePlace K), ∃ z, v (pr w z) = nrm B v w ^ 2 ∧ nrm M v z = nrm B v w

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

@[reducible] def lat : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 K) K))

def dot : (lat K n).V →ₗ[K] Module.Dual K (lat K n).V := dotProductBilin K K

variable {K n}

end Std

end GlobalTheory.Core.Ht2

end

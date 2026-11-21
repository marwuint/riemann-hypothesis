import Mathlib
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import GroundTheory.AutomorphicForms.HermitianLocalForms

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global NumberField.InfinitePlace.Completion

def Rep {F : Type*} [Field F] (d : F) {n : ℕ} (a : Fin n → F) (c : F) : Prop :=
  ∃ s : Fin n → F, (∀ i, SqNorm d (s i)) ∧ ∑ i, a i * s i = c

end GroundTheory.Automorphic

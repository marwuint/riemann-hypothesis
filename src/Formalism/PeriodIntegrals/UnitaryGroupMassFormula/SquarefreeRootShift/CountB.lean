import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

def Good (c : (ZMod g)ˣ) (P : (ZMod g)[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ j : ℕ,
    P ∣ X ^ (ℓ ^ j) - C ((c : ZMod g) ^ (ℓ ^ j))

end PI.SqfRootShift.W

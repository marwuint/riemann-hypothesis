import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR

def DiffIndepStatement.{u, v} : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] (D : ℕ)
    (x : Fin D → Ω),
    LinearIndependent Ω (fun k => KaehlerDifferential.D K Ω (x k)) → AlgebraicIndependent K x

end ReciprocityTheory.ChartRestriction.G.AR

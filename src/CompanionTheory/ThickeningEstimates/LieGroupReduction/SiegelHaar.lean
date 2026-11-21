import Mathlib
import Formalism.UnipotentAdelicQuotients.HaarProductClosedCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarProductClosedCompactHolds

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise

namespace CompanionTheory.ThKR.Sieg

section Heis

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

@[nolint unusedArguments]
def Heis (_ : A →+ A →+ B) : Type := A × B

variable (β : A →+ A →+ B)

instance : Group (Heis β) where
  mul x y := (x.1 + y.1, x.2 + y.2 + β x.1 y.1)
  one := (0, 0)
  inv x := (-x.1, -x.2 + β x.1 x.1)
  mul_assoc x y z := Prod.ext (add_assoc _ _ _) (by
    change x.2 + y.2 + β x.1 y.1 + z.2 + β (x.1 + y.1) z.1 = x.2 + (y.2 + z.2 + β y.1 z.1) + β x.1 (y.1 + z.1)
    simp only [map_add, AddMonoidHom.add_apply]
    abel)
  one_mul x := Prod.ext (zero_add _) (by change 0 + x.2 + β 0 x.1 = x.2; simp)
  mul_one x := Prod.ext (add_zero _) (by change x.2 + 0 + β x.1 0 = x.2; simp)
  inv_mul_cancel x := Prod.ext (neg_add_cancel _) (by
    change -x.2 + β x.1 x.1 + x.2 + β (-x.1) x.1 = 0; simp)

theorem Heis.mul_def (x y : Heis β) : x * y = (x.1 + y.1, x.2 + y.2 + β x.1 y.1) := rfl

theorem Heis.inv_def (x : Heis β) : x⁻¹ = (-x.1, -x.2 + β x.1 x.1) := rfl

variable [TopologicalSpace A] [TopologicalSpace B]

instance : TopologicalSpace (Heis β) := inferInstanceAs (TopologicalSpace (A × B))

instance [T2Space A] [T2Space B] : T2Space (Heis β) := inferInstanceAs (T2Space (A × B))

instance [LocallyCompactSpace A] [LocallyCompactSpace B] : LocallyCompactSpace (Heis β) :=
  inferInstanceAs (LocallyCompactSpace (A × B))

instance [SecondCountableTopology A] [SecondCountableTopology B] : SecondCountableTopology (Heis β) :=
  inferInstanceAs (SecondCountableTopology (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] : MeasurableSpace (Heis β) :=
  inferInstanceAs (MeasurableSpace (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] :
    BorelSpace (Heis β) := inferInstanceAs (BorelSpace (A × B))

variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

end Heis

end CompanionTheory.ThKR.Sieg

end

import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticesTheory

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_star_int (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

end

end Formalism.HermitianLatticesTheory

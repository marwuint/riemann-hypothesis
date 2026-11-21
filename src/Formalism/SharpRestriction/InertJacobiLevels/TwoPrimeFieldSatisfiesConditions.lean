import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

end Base

section Indep

variable (u0 u0' : R.A) (ex ex' : Finset ℕ)

theorem twoPrimeField_base_unit : (host2 B u0 ex).u0 = u0 := rfl
theorem twoPrimeField_modulus : (host2 B u0 ex).q = B.q := rfl
theorem twoPrimeField_discriminant : (host2 B u0 ex).d = B.d := rfl
theorem twoPrimeField_generators : (host2 B u0 ex).g = ![B.g0, B.g1] := rfl
theorem twoPrimeField_firstPrime : (host2 B u0 ex).pde = B.pde := rfl
theorem twoPrimeField_secondPrime : (host2 B u0 ex).pde' = B.pde' := rfl
theorem twoPrimeField_torsionSet : (host2 B u0 ex).TT = B.TT := rfl
theorem host2_T2_eq : (host2 B u0 ex).T2 = B.T2 := rfl
theorem twoPrimeField_weightLattice : (host2 B u0 ex).Lw = B.Lw := rfl
theorem twoPrimeField_errorConstant : (host2 B u0 ex).CT2 = CT := rfl
theorem twoPrimeField_splitBound : (host2 B u0 ex).splitBound = ⌊x ^ (eps / 5)⌋₊ := rfl
theorem twoPrimeField_field_eq : (host2 B u0 ex).E = B.E := rfl
theorem twoPrimeField_axioms : (host2 B u0 ex).toHostAx = B.toHostAx := rfl
theorem twoPrimeField_smallModulus : (host2 B u0 ex).QS = B.QS := rfl
theorem twoPrimeField_rootDiscriminant : (host2 B u0 ex).rdE = B.rd := rfl
theorem twoPrimeField_twistedNorm_iff (T : ℕ) : TNorm (host2 B u0 ex) T ↔ TNorm (host2 B u0' ex') T := Iff.rfl
theorem twoPrimeField_class_eq (p : ℕ) : (host2 B u0 ex).cls p = (host2 B u0' ex').cls p := rfl

end Indep

end Formalism.MainNotions.Inhab

end

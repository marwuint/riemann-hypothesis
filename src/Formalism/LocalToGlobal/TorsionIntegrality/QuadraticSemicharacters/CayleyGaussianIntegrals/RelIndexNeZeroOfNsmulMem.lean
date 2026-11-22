import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.InterIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RatFourSquares
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Lattice

instance periodLattice_finite (L : PeriodPair) : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice

def stdLatEquiv (L : PeriodPair) (m : Type*) : stdLat L m ≃+ (m → L.lattice) where
  toFun x := fun i => ⟨(x : m → ℂ) i, (mem_stdLat L m x).1 x.2 i⟩
  invFun y := ⟨fun i => (y i : ℂ), (mem_stdLat L m _).2 fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem stdLat_finite (L : PeriodPair) (m : Type*) [Finite m] : Module.Finite ℤ (stdLat L m) := Module.Finite.equiv (stdLatEquiv L m).symm.toIntLinearEquiv

end Lattice

end Formalism.L2.Th1.H

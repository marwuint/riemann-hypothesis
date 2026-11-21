import Mathlib
import Formalism.AlphaUniqueness.Statement
import Formalism.LatticeTheta.Statement
import Formalism.HermitianLattices.StatementLat

open Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

def thetaBasic_eqv {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) : L ≃ gmap g L where
  toFun x := ⟨g x, Submodule.mem_map_of_mem x.2⟩
  invFun y := ⟨g.symm y, by
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.2
    have hz' : g z = (y : V) := hzy
    rw [← hz', LinearEquiv.symm_apply_apply]
    exact hz⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem thetaBasic_eqv_apply {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) (x : L) :
    ((thetaBasic_eqv g L x : gmap g L) : V) = g x := rfl

end Formalism.HermitianLatticesTheory

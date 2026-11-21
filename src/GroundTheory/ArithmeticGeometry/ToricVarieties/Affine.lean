import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.IsFaceOfIffExistsEqExposedFace
import GroundTheory.ArithmeticGeometry.ToricVarieties.Lattice

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry

universe u

section SemigroupAlgebra

variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]

noncomputable def semigroupAlgebra (S : AddSubmonoid G) : Subalgebra k (AddMonoidAlgebra k G) :=
  (AddMonoidAlgebra.supported k k (S : Set G)).toSubalgebra
    (by
      rw [AddMonoidAlgebra.mem_supported]
      exact (Finset.coe_subset.2 (support_coeff_one_subset)).trans
        (by simp [S.zero_mem]))
    (by
      classical
      intro x y hx hy
      rw [AddMonoidAlgebra.mem_supported] at hx hy ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset x y hm)
      exact S.add_mem (hx ha) (hy hb))

variable {k}

theorem mem_semigroupAlgebra {S : AddSubmonoid G} {f : AddMonoidAlgebra k G} :
    f ∈ semigroupAlgebra k S ↔ ↑f.coeff.support ⊆ (S : Set G) := Iff.rfl

end SemigroupAlgebra

section Domain

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

theorem uniqueSums_of_free [Module.Free ℤ G] : UniqueSums G :=
  UniqueSums.of_injective_addHom
    ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
    (Module.Free.chooseBasis ℤ G).repr.injective inferInstance

instance isDomain_addMonoidAlgebra [IsDomain k] [Module.Free ℤ G] :
    IsDomain (AddMonoidAlgebra k G) :=
  haveI := uniqueSums_of_free (G := G)
  NoZeroDivisors.to_isDomain _

instance isDomain_semigroupAlgebra [IsDomain k] [Module.Free ℤ G] (S : AddSubmonoid G) :
    IsDomain (semigroupAlgebra k S) :=
  inferInstance

end Domain

section Toric

variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]

noncomputable abbrev toricAlgebra (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    Subalgebra k (AddMonoidAlgebra k (Dual ℤ N)) :=
  semigroupAlgebra k (dualMonoid σ)

noncomputable abbrev affineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : Scheme.{u} :=
  Spec (CommRingCat.of (toricAlgebra k σ))

variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]

instance affineToricVariety_isIntegral [IsDomain k] (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    IsIntegral (affineToricVariety k σ) :=
  inferInstance

end Toric

end GroundTheory.Arith.Toric

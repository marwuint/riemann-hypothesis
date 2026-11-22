import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds

namespace ReciprocityTheory.Coh
open Cx Function
noncomputable section
universe u

namespace ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem mem_B_zero (A : Cx R) (x : A.X 0) : x ∈ A.B 0 ↔ x = 0 := Submodule.mem_bot R
theorem mem_B_succ (A : Cx R) (n : ℕ) (x : A.X (n+1)) : x ∈ A.B (n+1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range

theorem H_cls (φ : Hom A B) (n : ℕ) (x : A.X n) (hx) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := rfl

end ProjectiveLinePlaces

open ProjectiveLinePlaces

end
end ReciprocityTheory.Coh

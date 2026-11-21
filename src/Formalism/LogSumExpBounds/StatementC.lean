import Mathlib

namespace Formalism.NuclearRankWeightBounds.C

open Matrix

section
variable (RR : Type*) (K : Type*) [CommRing RR] [CommRing K] [Algebra RR K]

abbrev KmodR : Type _ := K ⧸ LinearMap.range (Algebra.linearMap RR K)

variable {RR}

abbrev coker {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Type _ :=
  (Fin k → RR) ⧸ LinearMap.range Z.mulVecLin

def toK {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Matrix (Fin k) (Fin k) K :=
  Z.map (algebraMap RR K)

noncomputable def rowInvMod {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    (Fin k → RR) →ₗ[RR] KmodR RR K :=
  (Submodule.mkQ _).comp
    { toFun := fun v => ∑ i, ∑ j, r i * (toK K Z)⁻¹ i j * algebraMap RR K (v j)
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        rw [RingHom.id_apply]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }

noncomputable def descend {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    coker Z →ₗ[RR] KmodR RR K := by
  classical
  exact if hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r) then
    (LinearMap.range Z.mulVecLin).liftQ (rowInvMod K Z r) hZ else 0

variable {m : ℕ}

noncomputable def lam (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker Z →ₗ[RR] KmodR RR K :=
  descend K Z (Pi.single (Fin.last m) 1)

noncomputable def kappa (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  (toK K Z)⁻¹ (Fin.last m) (Fin.last m)

def blk (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Matrix (Fin m) (Fin m) RR :=
  Z.submatrix Fin.castSucc Fin.castSucc

noncomputable def cval (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  algebraMap RR K (Z (Fin.last m) (Fin.last m)) -
    ∑ i, ∑ j, algebraMap RR K (Z (Fin.last m) (Fin.castSucc i)) * (toK K (blk Z))⁻¹ i j *
      algebraMap RR K (Z (Fin.castSucc j) (Fin.last m))

noncomputable def alpha (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker (blk Z) →ₗ[RR] KmodR RR K :=
  descend K (blk Z) (fun j => algebraMap RR K (Z (Fin.last m) (Fin.castSucc j)))

end

end Formalism.NuclearRankWeightBounds.C

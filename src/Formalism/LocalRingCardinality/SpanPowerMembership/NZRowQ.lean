import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section TwoChar

variable {Z V : Type} [CommSemiring Z] [Algebra ℂ Z] [AddCommGroup V] [Module ℂ V]

def twoChar (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) : Z →ₐ[ℂ] Module.End ℂ V :=
  AlgHom.ofLinearMap (χ1.toLinearMap.smulRight E + χ0.toLinearMap.smulRight (1 - E))
    (by simp)
    (fun x y => by
      have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
      have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
      have hFF : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, hFE, sub_zero]
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, AlgHom.toLinearMap_apply, map_mul, add_mul,
        mul_add, smul_mul_smul_comm, hE, hEF, hFE, hFF, smul_zero, add_zero, zero_add])

theorem twoChar_apply (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) (z : Z) :
    twoChar χ1 χ0 E hE z = χ1 z • E + χ0 z • (1 - E) := rfl

end TwoChar

def MultT (EE A : Type) : ℕ → Type
  | 0 => EE
  | _ + 1 => A

section MultT

variable (EE A : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]

instance MultT.nacg : ∀ j, NormedAddCommGroup (MultT EE A j)
  | 0 => inferInstanceAs (NormedAddCommGroup EE)
  | _ + 1 => inferInstanceAs (NormedAddCommGroup A)

instance MultT.ips : ∀ j, InnerProductSpace ℂ (MultT EE A j)
  | 0 => inferInstanceAs (InnerProductSpace ℂ EE)
  | _ + 1 => inferInstanceAs (InnerProductSpace ℂ A)

instance MultT.fd : ∀ j, FiniteDimensional ℂ (MultT EE A j)
  | 0 => inferInstanceAs (FiniteDimensional ℂ EE)
  | _ + 1 => inferInstanceAs (FiniteDimensional ℂ A)

variable {EE A}

end MultT

section Coord

variable {n : ℕ} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  (b : OrthonormalBasis (Fin n) ℂ EE) (a n1 : ℕ) (hn : n ≤ n1) (h1 : n1 ≤ a)

def eP : En a →ₗ[ℂ] En a where
  toFun x := WithLp.toLp 2 fun i => if (i : ℕ) < n1 then x i else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]

theorem eP_apply (x : En a) (i : Fin a) : eP a n1 x i = if (i : ℕ) < n1 then x i else 0 := rfl

def secB : EE →ₗ[ℂ] En a where
  toFun y := WithLp.toLp 2 fun i => if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]

theorem secB_apply (y : EE) (i : Fin a) : secB b a y i = if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0 := rfl

end Coord

end Formalism.BasicNotions.Examples₂.NZ

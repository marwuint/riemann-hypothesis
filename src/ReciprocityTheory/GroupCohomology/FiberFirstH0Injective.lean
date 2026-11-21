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

theorem fib_d_snd_succ (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (((fib φ).d (n+1) x).2 : B.X (n+1)) = φ.f (n+1) x.1 - B.d n x.2 := by
  show φ.f (n+1) x.1 + -B.d n x.2 = _
  rw [sub_eq_add_neg]

theorem fib_d_succ_iff (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (fib φ).d (n+1) x = 0 ↔ A.d (n+1) x.1 = 0 ∧ φ.f (n+1) x.1 = B.d n x.2 := by
  constructor
  · intro h; exact ⟨congrArg Prod.fst h, sub_eq_zero.mp ((fib_d_snd_succ φ n x).symm.trans (congrArg Prod.snd h))⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 ((fib_d_snd_succ φ n x).trans (sub_eq_zero.mpr h2))

def fibIncl (φ : Hom A B) (n : ℕ) : B.Z n →ₗ[R] (fib φ).Z (n+1) where
  toFun b := ⟨(0, b.1), (fib_d_succ_iff φ n _).mpr ⟨map_zero _, by
    show φ.f (n+1) 0 = B.d n b.1
    rw [map_zero]; exact (b.2 : B.d n b.1 = 0).symm⟩⟩
  map_add' x y := Subtype.ext (Prod.ext (add_zero (0 : A.X (n+1))).symm rfl)
  map_smul' r x := Subtype.ext (Prod.ext (smul_zero r).symm rfl)

def fibδ (φ : Hom A B) (n : ℕ) : B.H n →ₗ[R] (fib φ).H (n + 1) :=
  Submodule.mapQ _ _ (fibIncl φ n) fun x hx => by
    change (x : B.X n) ∈ B.B n at hx
    show ((0, (x : B.X n)) : (fib φ).X (n+1)) ∈ (fib φ).B (n+1)
    refine (mem_B_succ (fib φ) n _).mpr ?_
    cases n with
    | zero =>
      rw [mem_B_zero] at hx
      exact ⟨0, by rw [map_zero, hx]; rfl⟩
    | succ m =>
      obtain ⟨y, hy⟩ := (mem_B_succ B m _).mp hx
      refine ⟨(0, -y), Prod.ext (map_zero (A.d (m+1))) ?_⟩
      refine (fib_d_snd_succ φ m _).trans ?_
      show φ.f (m+1) 0 - B.d m (-y) = (x : B.X (m+1))
      rw [map_zero, map_neg, zero_sub, neg_neg, hy]

theorem fibδ_cls (φ : Hom A B) (n : ℕ) (b : B.X n) (hb) (h) :
    fibδ φ n (B.cls n b hb) = (fib φ).cls (n + 1) (0, b) h := rfl

end ProjectiveLinePlaces

open ProjectiveLinePlaces

end
end ReciprocityTheory.Coh

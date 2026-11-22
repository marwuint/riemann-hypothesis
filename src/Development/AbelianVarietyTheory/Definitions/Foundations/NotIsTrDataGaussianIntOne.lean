import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section

namespace GlobalTheory.AlmostEt

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

structure IsDerOn (B : Subalgebra A S) (D : S → M) : Prop where
  add : ∀ x ∈ B, ∀ y ∈ B, D (x + y) = D x + D y
  mul : ∀ x ∈ B, ∀ y ∈ B, D (x * y) = x • D y + y • D x
  alg : ∀ a : A, D (algebraMap A S a) = 0

structure IsTrData (B C : Subalgebra A S) (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) : Prop where
  le : B ≤ C
  e_mem : e ∈ B
  a_mem : ∀ i, a i ∈ C
  b_mem : ∀ i, b i ∈ C
  tr_mem : ∀ x ∈ C, tr x ∈ B
  tr_add : ∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y
  tr_mul : ∀ β ∈ B, ∀ x ∈ C, tr (β * x) = β * tr x
  left : ∀ x ∈ C, ∑ i, a i * tr (b i * x) = e * x
  right : ∀ x ∈ C, ∑ i, b i * tr (a i * x) = e * x
  sum : ∑ i, a i * b i = e

end General

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simpa using T.q0
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

def zS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.ζ n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [(T.prim n).pow_eq_one]; exact isIntegral_one)⟩

def qS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.qq n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [qq_pow]; exact isIntegral_algebraMap)⟩

def levelAlg (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) {zS T n, qS T n}

def towerAlg (T : Tower p Ω) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) (Set.range (zS T) ∪ Set.range (qS T))

abbrev Frac (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ :=
  Ω ⧸ LinearMap.range (Algebra.linearMap (integralClosure (O0 p) Ω) Ω)

end Tower

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.Inhab

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

end Tower

end GlobalTheory.AlmostEt.Inhab

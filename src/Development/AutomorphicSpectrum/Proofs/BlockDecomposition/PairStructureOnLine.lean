import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Fin n × Fin n

abbrev Ix (n : ℕ) : Type := Bool × Pos n

abbrev Cr (n : ℕ) (V : Type) : Type := Finset (Ix n) → V

def keyR (i : Ix n) : ℕ := (if i.1 then n * n else 0) + CompanionTheory.D.LK.key i.2

def sgR (i : Ix n) (A : Finset (Ix n)) : ℂ := (-1) ^ (A.filter fun j => keyR j < keyR i).card

def cp (p q r : Pos n) : ℂ :=
  (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then 1 else 0) - (if q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2) then 1 else 0)

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then 0 else sgR i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def creR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then sgR i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def liftR (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cr n V →ₗ[ℂ] Cr n V' :=
  T.compLeft (Finset (Ix n))

def rl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Ix n) : Module.End ℂ V :=
  if i.1 then E1 i.2.1.1 i.2.1.2 + E2 i.2.1.1 i.2.1.2 else E2 i.2.1.1 i.2.1.2

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Lt n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2.1 p.2.2 else E2 p.2.1 p.2.2

structure Pair2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

end Chains

def Inv2 (a : FreeAlgebra ℂ (Lt n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def LiftInv : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Pair2 E1 E2 → (∀ a b (x y : V), inner ℂ (kF E1 E2 a b x) y = inner ℂ x (kF E1 E2 b a y)) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ (μ : Fin n → ℝ) (v w : V), v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a : FreeAlgebra ℂ (Lt n), Inv2 a ∧ ev2 E1 E2 a v = w

end GlobalTheory.CompanionTheory.RealMult

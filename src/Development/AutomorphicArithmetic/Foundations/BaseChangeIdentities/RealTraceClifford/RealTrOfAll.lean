import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace UpperTheory.RealTr

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev UK (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

section U

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def coef (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def KSt (S : Submodule ℂ U) : Prop := ∀ k : UK n, ∀ v ∈ S, π (uG k) v ∈ S

def kfin : Submodule ℂ U where
  carrier := {v | ∃ S : Submodule ℂ U, FiniteDimensional ℂ S ∧ KSt π S ∧ v ∈ S}
  add_mem' := by
    rintro a b ⟨S, hS, kS, ha⟩ ⟨S', hS', kS', hb⟩
    refine ⟨S ⊔ S', inferInstance, fun k v hv => ?_, Submodule.add_mem_sup ha hb⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (kS k x hx) (kS' k y hy)
  zero_mem' := ⟨⊥, inferInstance, fun k v hv => by simp_all, Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨S, hS, kS, ha⟩
    exact ⟨S, hS, kS, S.smul_mem c ha⟩

theorem kfin_stable : KSt π (kfin π) := by
  rintro k v ⟨S, hS, kS, hv⟩
  exact ⟨S, hS, kS, kS k v hv⟩

theorem uG_mul (k k' : UK n) : uG (k * k') = uG k * uG k' := map_mul Unitary.toUnits k k'

theorem uG_one : uG (1 : UK n) = 1 := map_one Unitary.toUnits

def sig : UK n →* (kfin π →ₗ[ℂ] kfin π) where
  toFun k := (π (uG k) : U →ₗ[ℂ] U).restrict (kfin_stable π k)
  map_one' := by ext v; simp [uG_one]
  map_mul' k k' := by ext v; simp [uG_mul]

@[simp] theorem sig_coe (k : UK n) (v : kfin π) : (sig π k v : U) = π (uG k) v := rfl

end U

def KerReg (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) ∧
    ∀ y ∈ GLs n, ∀ k₁ k₂ : UK n, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂

end UpperTheory.RealTr

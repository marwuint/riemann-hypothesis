import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

set_option linter.style.haveILetI false

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section TP

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

def tsumP (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) : Matrix (Fin n) (Fin n) K :=
  haveI : Fintype H := Fintype.ofFinite H
  ∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • ρ (h : Γ)

theorem typeProj_eq (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    typeProj ρ H χ = ((Nat.card H : K)⁻¹) • tsumP ρ H χ := rfl

variable [NumberField K]

end TP

section Norms

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

theorem maj_eq (v : InfinitePlace K) (x y : Fin n → K) :
    majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fcoord (Pi.basisFun K (Fin n)) X v x) ⬝ᵥ fcoord (Pi.basisFun K (Fin n)) X v y := rfl

end Norms

section Gen

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem rows_gen (hL : A.LatG) {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hD : 0 < D) (hinj : Function.Injective ι.mulVec) (hr : LinearMap.range ι.mulVecLin = LinearMap.range P.mulVecLin) :
    A.partLat P ≠ ⊥ := by
  intro hb
  have hspan := A.span_partLat hL P
  rw [hb, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  obtain ⟨x, hx⟩ : ∃ x : Fin D → K, x ≠ 0 := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hD⟩)⟩
  have hmem : ι *ᵥ x ∈ LinearMap.range P.mulVecLin := by
    rw [← hr]
    exact ⟨_, rfl⟩
  rw [← hspan, Submodule.mem_bot] at hmem
  exact hx (hinj (by rw [hmem, Matrix.mulVec_zero]))

end Gen

end Formalism.L2.GlobalTheoryTheory.DivPassage2

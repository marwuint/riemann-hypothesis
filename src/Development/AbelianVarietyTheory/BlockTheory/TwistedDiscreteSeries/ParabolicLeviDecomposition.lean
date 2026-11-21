import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.SmGL GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped NNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition

structure ParabLevi (k : Type) [Field k] (r : ℕ) where

  s : ℕ

  d : Fin s → ℕ

  e : (Σ a, Fin (d a)) ≃ Fin r

  g : GL (Fin r) k

namespace ParabLevi

variable {k : Type} [Field k] {r : ℕ} (P : ParabLevi k r)

def coord : GL (Fin r) k →* GL (Fin r) k := (MulAut.conj P.g⁻¹).toMonoidHom

theorem coord_apply (x : GL (Fin r) k) : P.coord x = P.g⁻¹ * x * P.g := by simp [coord]

def Q : Subgroup (GL (Fin r) k) := (parab k P.e).comap P.coord

def M : Subgroup (GL (Fin r) k) := (leviEmb k P.e).range.comap P.coord

def lieN : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, blk P.e j ≤ blk P.e i →
    ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) i j = 0}
  zero_mem' := fun i j _ => by simp
  add_mem' := fun {X Y} hX hY i j h => by
    rw [mul_add, add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  smul_mem' := fun c X hX i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

theorem M_le_Q : P.M ≤ P.Q := by
  rintro x ⟨y, hy⟩
  change P.coord x ∈ parab k P.e
  exact hy ▸ leviEmb_mem_parab k P.e y

theorem conj_mem_lieN {q : GL (Fin r) k} (hq : q ∈ P.Q) {X : Matrix (Fin r) (Fin r) k} (hX : X ∈ P.lieN) :
    q.1 * X * (q⁻¹ : GL (Fin r) k).1 ∈ P.lieN := by
  intro i j h
  have e : (P.g⁻¹ : GL (Fin r) k).1 * (q.1 * X * (q⁻¹ : GL (Fin r) k).1) * P.g.1 =
      (P.coord q).1 * ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) * (P.coord q⁻¹).1 := by
    simp only [coord_apply, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
  have h1 := mem_parab.1 (show P.coord q ∈ parab k P.e from hq)
  have h2 := mem_parab.1 (show P.coord q⁻¹ ∈ parab k P.e from P.Q.inv_mem hq)
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : blk P.e j < blk P.e b
  · rw [h2 b j hb, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => ?_, zero_mul]
    by_cases ha : blk P.e a < blk P.e i
    · rw [h1 i a ha, zero_mul]
    · rw [hX a b (((not_lt.1 hb).trans h).trans (not_lt.1 ha)), mul_zero]

def adN (q : P.M) : P.lieN →ₗ[k] P.lieN :=
  (LinearMap.mulLeftRight k (q.1.1, (q.1⁻¹ : GL (Fin r) k).1)).restrict fun _ hX =>
    P.conj_mem_lieN (P.M_le_Q q.2) hX

theorem coe_adN (q : P.M) (X : P.lieN) :
    (P.adN q X : Matrix (Fin r) (Fin r) k) = q.1.1 * X * (q.1⁻¹ : GL (Fin r) k).1 := rfl

end ParabLevi

variable (F : Type) [Field F] [NumberField F] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))

variable {F r S} (P : ∀ v : S, ParabLevi (Fv F v.1) r)

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition

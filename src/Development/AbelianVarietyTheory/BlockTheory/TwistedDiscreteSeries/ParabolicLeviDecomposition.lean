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

end ParabLevi

variable (F : Type) [Field F] [NumberField F] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))

variable {F r S} (P : ∀ v : S, ParabLevi (Fv F v.1) r)

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition

import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible

open ReciprocityTheory.Ty.Fin CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdSimple

def cf {Γ : Type} [Group Γ] (g : Γ) : MonoidAlgebra ℂ Γ →ₗ[ℂ] ℂ where
  toFun a := a.coeff g
  map_add' a b := by simp
  map_smul' r a := by simp

theorem cf_apply {Γ : Type} [Group Γ] (g : Γ) (a : MonoidAlgebra ℂ Γ) : cf g a = a.coeff g := rfl

variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

end GlobalTheory.CompanionTheory.ProdSimple


import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible

open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinJacquet

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

def blockHom (b : ι → Fin s) : (∀ c, Matrix {i // b i = c} {i // b i = c} K) →* Matrix ι ι K where
  toFun M := (Matrix.blockDiagonal' M).submatrix (Equiv.sigmaFiberEquiv b).symm (Equiv.sigmaFiberEquiv b).symm
  map_one' := by
    rw [Matrix.blockDiagonal'_one]
    simp
  map_mul' M N := by
    show (Matrix.blockDiagonal' (fun k => M k * N k)).submatrix _ _ = _
    rw [Matrix.blockDiagonal'_mul, Matrix.submatrix_mul_equiv]

def dGL (b : ι → Fin s) : (∀ c, GL {i // b i = c} K) →* GL ι K :=
  (Units.map (blockHom b)).comp
    (MulEquiv.piUnits (M := fun c => Matrix {i // b i = c} {i // b i = c} K)).symm.toMonoidHom

end GlobalTheory.CompanionTheory.TyFinJacquet

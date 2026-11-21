import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section AntiTranspose

variable {R : Type*} [CommRing R]

def antiTr (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

theorem antiTr_mul (A B : Matrix (Fin 2) (Fin 2) R) : antiTr (A * B) = antiTr B * antiTr A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiTr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem antiTr_one : antiTr (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

def antiTrGL (g : GL (Fin 2) R) : GL (Fin 2) R where
  val := antiTr (g : Matrix (Fin 2) (Fin 2) R)
  inv := antiTr ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  val_inv := by rw [← antiTr_mul, Units.inv_mul, antiTr_one]
  inv_val := by rw [← antiTr_mul, Units.mul_inv, antiTr_one]

theorem coe_antiTrGL (g : GL (Fin 2) R) :
    (antiTrGL g : Matrix (Fin 2) (Fin 2) R) = antiTr (g : Matrix (Fin 2) (Fin 2) R) := rfl

end AntiTranspose

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end GlobalTheory.CompanionTheory.LFUDom

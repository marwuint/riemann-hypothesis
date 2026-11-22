import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

def blockOf {m o : Type} (N : Matrix (m × o) (m × o) ℂ) (i : o) : Matrix m m ℂ := Matrix.of fun I K => N (I, i) (K, i)

theorem blockOf_add {m o : Type} (N N' : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N + N') i = blockOf N i + blockOf N' i := rfl

theorem blockOf_smul {m o : Type} (c : ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (c • N) i = c • blockOf N i := rfl

variable {m o : Type} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

variable (X) in

def phi (d : ℕ) {k : ℕ} (b : Fin k → A) :
    Matrix ((Fin d → Fin n) × Fin k) ((Fin d → Fin n) × Fin k) ℂ →ₗ[ℂ] A where
  toFun N := ∑ i, wordMap X d (blockOf N i) * b i
  map_add' N N' := by simp [blockOf_add, add_mul, Finset.sum_add_distrib]
  map_smul' c N := by simp [blockOf_smul, Finset.smul_sum, smul_mul_assoc]

theorem phi_apply (d : ℕ) {k : ℕ} (b : Fin k → A) (N) : phi X d b N = ∑ i, wordMap X d (blockOf N i) * b i := rfl

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC

end GlobalTheory.LeviHC

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagU {R : Type} [CommRing R] (u : n → Rˣ) : GL n R where
  val := Matrix.diagonal fun j => (u j : R)
  inv := Matrix.diagonal fun j => (((u j)⁻¹ : Rˣ) : R)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

def cycSum (K : FinExt l) (a : n → ℤ) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) where
  toFun g := diagU fun j => Units.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) : ℚ_[l] →* ↥(MaximalUnramifiedExtension l)) (P.χQ (g : GQ l) ^ a j)
  map_one' := by ext i j; simp [diagU]
  map_mul' g h := by
    apply Units.ext
    simp [diagU, Matrix.diagonal_mul_diagonal, mul_zpow]

theorem cycSum_val (K : FinExt l) (a : n → ℤ) (g : ↥(GK K)) : (cycSum P K a g : Matrix n n ↥(MaximalUnramifiedExtension l)) =
    Matrix.diagonal fun j => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((P.χQ (g : GQ l) ^ a j : ℚ_[l]ˣ) : ℚ_[l]) := rfl

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

end GlobalTheory.PMon.Model

end

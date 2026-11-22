import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker GlobalTheory.IndefiniteRowSideFullHecke Filter Topology
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.VacuumFrameCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem af_ext {α β : Af D.host.F} (h : ∀ w, evalV D.host.F w α = evalV D.host.F w β) : α = β :=
  FiniteAdeleRing.ext _ h

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from af_ext fun w => ?_)
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

def cut {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) : Rˣ where
  val := 1 + η * ((x : R) - 1)
  inv := 1 + η * (((x⁻¹ : Rˣ) : R) - 1)
  val_inv := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this
  inv_val := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this

theorem cut_val {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) :
    (cut η h x : R) = 1 + η * ((x : R) - 1) := rfl

theorem cut_inv {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) :
    (((cut η h x)⁻¹ : Rˣ) : R) = 1 + η * (((x⁻¹ : Rˣ) : R) - 1) := rfl

end GlobalTheory.VacuumFrameCompare

end

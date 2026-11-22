import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel

noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def ech (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

def sch {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : Y → ℂ) : Y → ℂ :=
  fun x => ech (β x b + β a b / 2) * f (x + a)

variable (F : Type) [Field F] [NumberField F]

def arch {κ : Type} (v : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (v i)

def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def liftA (ξ : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ)

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}

end GlobalTheory.ArchSch

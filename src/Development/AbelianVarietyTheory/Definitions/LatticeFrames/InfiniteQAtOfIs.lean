import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDoubleDescentRanksOneThreeFive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToOneSpherical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.PinTest
open GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem prX_KO {c : ℕ} : prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (KO k (n ⊕ Fin c)) 1) → IntM g.val := by
    rintro g ⟨u, hu, h⟩ i j
    have h2 := (mem_KO.1 (mem_Cgrp.1 h).2).1 (Sum.inl i) (Sum.inl j)
    have h3 : (u * embX c g).val.toBlocks₁₁ = g.val := by
      rw [Units.val_mul, mul_toBlocks₁₁, Radical.toBlocks₁₁_of_mem hu]
      change 1 * (fromBlocks g.val 0 0 1).toBlocks₁₁ + _ * (fromBlocks g.val 0 0 1).toBlocks₂₁ = _
      simp
    rw [inv_one, one_mul, mul_one] at h2
    rw [← h3]; exact h2
  ext g
  refine ⟨fun h => mem_KO.2 ⟨key g h, key _ (inv_mem h)⟩, fun h => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩⟩
  · rw [one_mul]; exact Subgroup.mem_sup_left ⟨g, rfl⟩
  · rw [inv_one, one_mul, one_mul, mul_one]
    refine mem_KO.2 ⟨intM_fromBlocks.2 ⟨(mem_KO.1 h).1, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩, ?_⟩
    rw [← map_inv]
    exact intM_fromBlocks.2 ⟨(mem_KO.1 h).2, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩

variable {s : ℕ} (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
include hψ hν

theorem isOneComb_sph {c P : ℕ} (h1 : 1 ≤ P) (h2 : P ≤ c) : IsOneComb ψ ν P (sph k (n ⊕ Fin c)) 1 (Finsupp.single 1 1) :=
  fun A _ _ σ hσ l hl v hv => by
  rw [map_one, Module.End.one_apply, GlobalTheory.PosOneSpherical.toOne_spherical k n c P h1 h2 ψ hψ.continuous hψ ν hν A σ hσ l hl v
    fun g hg => (hv ⟨g, hg⟩).trans (one_smul ℂ v)]
  simp [GlobalTheory.PosOne.comb]

end Local

variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

end GlobalTheory.QPl.PinTest
end

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sum_orth {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c : ι → K) (i : ι) : h (b i) (∑ j, c j • b j) = c i * h (b i) (b i) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [ho i j (Ne.symm hji), mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]

end

end Formalism.L2.SG.Pf.G3

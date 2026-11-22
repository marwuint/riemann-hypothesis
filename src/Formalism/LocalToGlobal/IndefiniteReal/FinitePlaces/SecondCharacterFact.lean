import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Places

variable {F : Type} [Field F] [NumberField F]

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  have h2 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
  have hv1 : v.valuation F x ≤ 1 := not_lt.1 hv.1
  have hv2 : v.valuation F x⁻¹ ≤ 1 := not_lt.1 hv.2
  have hpos : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have hval : v.valuation F x = 1 := by
    rw [map_inv₀, inv_le_one₀ hpos] at hv2
    exact le_antisymm hv1 hv2
  have h := NumberField.FinitePlace.norm_def' (K := F) v x
  rw [hval] at h
  simp only [map_one, NNReal.coe_one] at h
  exact h

end Places

variable {D : D7}

end Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end

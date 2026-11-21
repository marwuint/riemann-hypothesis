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

theorem compA_inf (Δ P R : F) (a b : AF F) (w : InfinitePlace F) :
    (a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).1 w =
      a.1 w * algebraMap F w.Completion P + algebraMap F w.Completion Δ * (b.1 w * -algebraMap F w.Completion R) := rfl

theorem compB_inf (P R : F) (a b : AF F) (w : InfinitePlace F) :
    (a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).1 w =
      a.1 w * -algebraMap F w.Completion R + b.1 w * algebraMap F w.Completion P := rfl

theorem compA_fin (Δ P R : F) (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * algebraMap F (AF F) P + algebraMap F (AF F) Δ * (b * -algebraMap F (AF F) R)).2 v =
      a.2 v * algebraMap F (v.adicCompletion F) P +
        algebraMap F (v.adicCompletion F) Δ * (b.2 v * -algebraMap F (v.adicCompletion F) R) := rfl

theorem compB_fin (P R : F) (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * -algebraMap F (AF F) R + b * algebraMap F (AF F) P).2 v =
      a.2 v * -algebraMap F (v.adicCompletion F) R + b.2 v * algebraMap F (v.adicCompletion F) P := rfl

end Places

variable {D : D7}

end Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end

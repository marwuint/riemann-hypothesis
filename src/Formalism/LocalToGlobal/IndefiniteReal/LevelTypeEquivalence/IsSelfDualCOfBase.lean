import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SelfDualLatticeIsSelfDual
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSelfDualC_of_base {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ N) : IsSelfDualC V Λ := by
  obtain ⟨-, hdual, hN, hin, hout⟩ := hB
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hl0 := (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.self_dual_lattice_is_self_dual V).1
  let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hφ : ∀ x, φ x = (N : D.host.E) • x := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) x, map_natCast]
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · have hφinj : Function.Injective φ := fun a b hab => by
      rw [hφ, hφ] at hab
      exact smul_right_injective _ hN0 hab
    have hle : Λ.map φ ≤ Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set, hφ]
      exact hout x hx
    have : IsNoetherian (𝓞 D.host.E) (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V) := isNoetherian_of_fg_of_noetherian _ hl0.fg
    have h1 : ((Λ.map φ).comap (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective φ hφinj h2
  · rw [eq_top_iff, ← hl0.span_eq_top, Submodule.span_le]
    intro x hx
    have hNx : (N : D.host.E) • x ∈ Λ := hin x ((Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set V x).1 hx)
    have : x = (N : D.host.E)⁻¹ • ((N : D.host.E) • x) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
    have key : (N : D.host.E)⁻¹ • ((N : D.host.E) • x) ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span hNx)
    rw [← this] at key
    exact key
  · rw [Formalism.IndefR.Eqv.dual_of_dualL hdual y]
    simp only [Formalism.UG.hform, starRingEnd_apply, RingHom.mem_range]

end Formalism.IndefR.Eqv.KerDiag

end

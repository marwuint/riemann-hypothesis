import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke

set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CovTop.ne_bot_of_isLattice_coords {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) {d : ℕ} (hd : 0 < d) (b : Fin d → V) (hb : LinearIndependent K b)
    (hM : Submodule.IsLattice K (M.comap ((Fintype.linearCombination K b).restrictScalars O))) : M ≠ ⊥ := by
  rintro rfl
  have hinj : Function.Injective (Fintype.linearCombination K b) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by rwa [Fintype.linearCombination_apply] at hc))
  have h0 : (⊥ : Submodule O V).comap ((Fintype.linearCombination K b).restrictScalars O) = ⊥ := by
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 hinj
  have h := hM.span_eq_top
  rw [h0] at h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp at h


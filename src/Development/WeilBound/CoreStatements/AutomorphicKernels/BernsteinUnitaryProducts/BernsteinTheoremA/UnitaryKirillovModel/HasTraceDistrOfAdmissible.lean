import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.KirillovEndUnitaryOfTheoremA
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.LevelSmulSmul
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_testProj : ∃ Pr : (G → ℂ) →ₗ[ℂ] testFn G, ∀ f : testFn G, Pr f = f := by
  obtain ⟨Pr, hPr⟩ := LinearMap.exists_leftInverse_of_injective (testFn G).subtype (Submodule.ker_subtype _)
  exact ⟨Pr, fun f => LinearMap.congr_fun hPr f⟩

theorem fd_range_heckeLin_comp (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V}
    (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) (S : Module.End ℂ V) :
    FiniteDimensional ℂ (LinearMap.range (heckeLin μ hρ.1 f ∘ₗ S)) := by
  have := finiteDimensional_range_heckeLin μ hρ f
  exact Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

def traceD (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) : Module.End ℂ V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun S f => finTrace (heckeLin μ hρ.1 (Pr f) ∘ₗ S))
    (fun S₁ S₂ f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S₁
      have := fd_range_heckeLin_comp μ hρ (Pr f) S₂
      rw [LinearMap.comp_add]
      exact finTrace_add _ _)
    (fun c S f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S
      rw [LinearMap.comp_smul, smul_eq_mul]
      exact finTrace_smul _ _)
    (fun S f₁ f₂ => by
      have := fd_range_heckeLin_comp μ hρ (Pr f₁) S
      have := fd_range_heckeLin_comp μ hρ (Pr f₂) S
      rw [map_add, heckeLin_add μ hρ.1, LinearMap.add_comp]
      exact finTrace_add _ _)
    (fun c S f => by
      have := fd_range_heckeLin_comp μ hρ (Pr f) S
      rw [map_smul, heckeLin_smul μ hρ.1, LinearMap.smul_comp, smul_eq_mul]
      exact finTrace_smul _ _)

theorem traceD_apply (μ : Measure G) [μ.IsHaarMeasure] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (S : Module.End ℂ V) (f : G → ℂ) :
    traceD μ hρ Pr S f = finTrace (heckeLin μ hρ.1 (Pr f) ∘ₗ S) := rfl

end Gen

end PositivityTheory.PfBern.Unit

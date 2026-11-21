import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem twtr_cont_of_mem (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) : Continuous ψ.1 :=
  GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level

theorem twtr_integrable (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {f : GA E n → ℂ} (hf : Continuous f) (x : GA E n) :
    Integrable (fun y : H E n 0 => φ y * f (x * y.1)) μ := by
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => μ.finiteAt_nhdsWithin x K⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hφ.1.mul (hf.comp (continuous_const.mul continuous_fst))
  · exact hφ.2.mul_right

end

end DiscreteGroups.T1.G

end

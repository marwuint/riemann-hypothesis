import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem countable_GL (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH : Countable (ratH E n 0) := by
  have := countable_GL (E := E) n
  have := countable_GL (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable

theorem integral_mul_right_fd (D : Dom E n 0) (h : H E n 0) (f : H E n 0 → ℂ)
    (hf : ∀ (γ : ratH E n 0) x, f ((γ : H E n 0) * x) = f x) :
    ∫ x, f (x * h) ∂D.ν = ∫ x, f x ∂D.ν := by
  have := D.haar.1
  have := D.haar.2.1
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => measurable_const_mul (γ : H E n 0)⟩
  have : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have := countable_ratH (E := E) (n := n)
  have hmp : MeasurePreserving (fun x => x * h) D.μ D.μ := measurePreserving_mul_right D.μ h
  have hme : MeasurableEmbedding (fun x : H E n 0 => x * h) := (MeasurableEquiv.mulRight h).measurableEmbedding
  set s : Set (H E n 0) := (fun y => y * h⁻¹) ⁻¹' D.F with hs_def
  have hs : (fun x => x * h) ⁻¹' s = D.F := by
    ext x
    simp [hs_def]
  have hfd : IsFundamentalDomain (ratH E n 0) s D.μ :=
    D.fd.preimage_of_equiv (measurePreserving_mul_right D.μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ y => mul_assoc (γ : H E n 0) y h⁻¹
  calc ∫ x, f (x * h) ∂D.ν = ∫ x in (fun x => x * h) ⁻¹' s, f (x * h) ∂D.μ := by rw [hs]; rfl
    _ = ∫ y in s, f y ∂D.μ := hmp.setIntegral_preimage_emb hme f s
    _ = ∫ y in D.F, f y ∂D.μ := hfd.setIntegral_eq D.fd fun γ x => hf γ x
    _ = ∫ x, f x ∂D.ν := rfl

end DiscreteGroups.T1.G

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.CuspModel

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_ofChar (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) (e : ψ = χ⁻¹) :
    DualCl (IrrGL.ofChar χ hχ) (IrrGL.ofChar ψ hψ) := by
  subst e
  exact ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ⁻¹ hψ, rfl, rfl,
    ProjLine.nonempty_equiv_contra_ofChar (χ := detChar (Fin 1) χ) hχ.detChar⟩

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r rc : IrrGL (w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspModel

end

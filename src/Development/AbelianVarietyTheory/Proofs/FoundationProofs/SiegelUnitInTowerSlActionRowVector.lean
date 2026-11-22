import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelSL

theorem isOpen_Hs : IsOpen Hs := GlobalTheory.KZ.SiegelModel.isOpen_Hs

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := GlobalTheory.KZ.SiegelModel.neBot_Hs

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  apply Filter.Germ.coe_eq.2
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  exact h z hz

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  simp [sgC, UpperHalfPlane.ofComplex_apply]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_injective {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) :
    Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} {f : T.K}
    (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) : siegel T c x = f := by
  have hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  apply an_injective T
  rw [siegel, dif_pos hex, hex.choose_spec, hf]

theorem sl_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  intro Ω _ _ _ ε T c x γ hx
  symm
  apply siegel_eq
  rw [T.an_sl _ _ _ (_root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c x hx)]
  apply germ_eq_of_eqOn
  intro z hz
  have hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl
  rw [← hτ, mob_ofSL, sgC_coe, sgC_coe, GlobalTheory.T.siegel_function_transformation c x γ _ hx]

end GlobalTheory.KZ.SiegelSL


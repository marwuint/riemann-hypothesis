import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := GlobalTheory.KZ.SiegelModel.neBot_Hs

theorem siegel_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), admitted c x → siegel T c x ≠ 0 := by
  intro Ω _ _ _ ε T c x hx h0
  have han := _root_.GlobalTheory.KZ.SiegelMem.an_siegel_eq Ω ε T c x hx
  rw [h0, map_zero] at han
  have hev : (fun z => sgC c x z) =ᶠ[Filter.codiscreteWithin Hs] (fun _ => (0 : ℂ)) :=
    (Filter.Germ.coe_eq.1 han.symm)
  have hne : ∀ᶠ z in Filter.codiscreteWithin Hs, sgC c x z ≠ 0 := by
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    have hz' : 0 < z.im := hz
    simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact sg_ne_zero c x _ hx
  haveI := codiscreteWithin_Hs_neBot
  obtain ⟨z, h1, h2⟩ := (hev.and hne).exists
  exact h2 h1

end GlobalTheory.KZ

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ.SiegelModel

open GlobalTheory.Sieg GlobalTheory.Sieg.Model

theorem isOpen_Hs : IsOpen Hs :=
  isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))
  have hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [hloc]
    infer_instance
  refine hne.mono ?_
  unfold Filter.codiscreteWithin
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  unfold sgC
  rw [UpperHalfPlane.ofComplex_apply]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε)

theorem an_injective : Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {c : ℕ} {x : Fin 2 → ℚ} {f : T.K} (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) :
    siegel T c x = f := by
  have hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  unfold siegel
  rw [dif_pos hex]
  exact an_injective T (hex.choose_spec.trans hf.symm)

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_siegel {c : ℕ} {x : Fin 2 → ℚ} (M : ℕ) (hM : 0 < M) (hd : DifferentiableOn ℂ (sgC c x) Hs)
    (hmod : ∀ (γ : SL(2, ℤ)) (τ : ℍ), sg c x (γ • τ) = sg c (act x γ) τ)
    (hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ)
    (hexp : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c (act x γ) τ)) :
    T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by

  have hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩ := by
    intro γ z hz
    rw [mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]
  have hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z := by
    intro γ hγ z hz
    rw [hγz γ z hz, hlev γ hγ, ← sgC_coe]
  have hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M))
        (sgC c x (mob (ofSL γ) z)) := by
    intro γ
    obtain ⟨a, n0, ha, hs⟩ := hexp γ
    refine ⟨a, n0, ha, fun z hz => ?_⟩
    rw [hγz γ z hz]
    exact hs ⟨z, hz⟩
  obtain ⟨f, hf⟩ := T.mem_q (sgC c x) M hM hd hlev' hexp'
  rw [siegel_eq T hf]
  exact hf

end GlobalTheory.KZ.SiegelModel

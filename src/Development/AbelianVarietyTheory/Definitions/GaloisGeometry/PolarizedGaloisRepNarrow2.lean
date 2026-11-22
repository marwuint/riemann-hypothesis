import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace WDRep

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def ineEig (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : Submodule ℂ V :=
  ⨅ σ : Ine (F := E) A, Module.End.eigenspace (a.ρ (ineIncl h σ)) (χ σ)

theorem mem_ineEig {a : WDRep h V} {χ : Ine (F := E) A → ℂ} {v : V} :
    v ∈ a.ineEig χ ↔ ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) v = χ σ • v := by
  simp [ineEig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

def Mono0Ine (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : Prop :=
  ∀ v ∈ a.ineEig χ, a.N v = 0

theorem Mono0.mono0Ine {a : WDRep h V} (ha : a.Mono0) (χ : Ine (F := E) A → ℂ) : a.Mono0Ine χ :=
  fun v _ => by rw [show a.N = 0 from ha]; rfl

theorem Iso.mono0Ine {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) {χ : Ine (F := E) A → ℂ}
    (ha : a.Mono0Ine χ) : b.Mono0Ine χ := by
  obtain ⟨e, h1, h2⟩ := hab
  intro u hu
  have hv : e.symm u ∈ a.ineEig χ := mem_ineEig.2 fun σ => e.injective (by
    rw [h1, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
    exact mem_ineEig.1 hu σ)
  rw [← LinearEquiv.apply_symm_apply e u, ← h2, ha _ hv, map_zero]

theorem mono0Ine_tw {a : WDRep h V} {χ : Ine (F := E) A → ℂ} (s : ℝ) :
    (a.tw s).Mono0Ine χ ↔ a.Mono0Ine χ := by
  have e : (a.tw s).ineEig χ = a.ineEig χ := by
    ext v; simp only [mem_ineEig, tw_ρ, deg_ineIncl, zpow_zero, one_smul]
  simp only [Mono0Ine, e, tw_N]

end WDRep

namespace WD

def mono0Ine (x : WD h) (χ : Ine (F := E) A → ℂ) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Mono0Ine χ)
    (fun _ _ hab => propext ⟨fun ha => WDRep.Iso.mono0Ine hab ha, fun hb => WDRep.Iso.mono0Ine hab.symm hb⟩) x

@[simp] theorem mono0Ine_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : mono0Ine (mk a) χ ↔ a.Mono0Ine χ :=
  ⟨WDRep.Iso.mono0Ine (iso_std a).symm, WDRep.Iso.mono0Ine (iso_std a)⟩

@[simp] theorem mono0Ine_lpTw (x : WD h) (s : ℝ) (χ : Ine (F := E) A → ℂ) :
    mono0Ine (lpTw x s) χ ↔ mono0Ine x χ := by
  induction x using ind with
  | hP n a => rw [lpTw_mk, mono0Ine_mk, mono0Ine_mk, WDRep.mono0Ine_tw]

end WD

end GlobalTheory.WeilDeligne

namespace GlobalTheory.GalNarrow2

end GlobalTheory.GalNarrow2

namespace GlobalTheory.Published

end GlobalTheory.Published

end

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

theorem res_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Dec (F := E) A := by
  rw [mem_Dec] at hσ ⊢
  have key : ∀ x, x ∈ (AlgEquiv.restrictScalars E σ) • A ↔ x ∈ σ • A := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  ext x
  rw [key, hσ]

theorem res_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Ine (F := E) A :=
  ⟨res_mem_Dec hσ.1, hσ.2⟩

theorem res_actsAs {q q' n a b : ℕ} (hq : q' = q ^ n) {σ : G E' Ω} (hσ : ActsAs A q' σ a b) :
    ActsAs A q (AlgEquiv.restrictScalars E σ) (n * a) (n * b) := by
  refine ⟨res_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [hq, ← pow_mul, ← pow_mul] at this
  exact this

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

def resW {n : ℕ} (hq : normV w' = normV w ^ n) : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalars E (σ : G E' Ω), by
    obtain ⟨a, b, hab⟩ := σ.2
    exact ⟨n * a, n * b, res_actsAs hq hab⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coe_resW {n : ℕ} (hq : normV w' = normV w ^ n) (σ : Weil h') :
    ((resW h h' hq σ : Weil h) : G E Ω) = AlgEquiv.restrictScalars E (σ : G E' Ω) := rfl

def resI : Ine (F := E') A →* Ine (F := E) A where
  toFun t := ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resW_ineIncl {n : ℕ} (hq : normV w' = normV w ^ n) (t : Ine (F := E') A) :
    resW h h' hq (ineIncl h' t) = ineIncl h (resI t) := rfl

end DiscreteGroups.sglob.DzType

end

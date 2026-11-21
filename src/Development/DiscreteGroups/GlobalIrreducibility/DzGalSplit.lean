import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands TensorProduct Module

namespace DiscreteGroups.sglob.DzType

section Split

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def gsplitEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin 1 → ℂ) × (Fin n → ℂ) where
  toFun v := (fun _ => v 0, fun j => v j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.cons (p.1 0) p.2
  left_inv v := Fin.cons_self_tail v
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Subsingleton.elim i 0]
      simp
    · simp

theorem gsplitEquiv_apply (n : ℕ) (v : Fin (n + 1) → ℂ) :
    gsplitEquiv n v = (fun _ => v 0, fun j => v j.succ) := rfl

end Split

end DiscreteGroups.sglob.DzType

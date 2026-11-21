import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.WeilRestrict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
  {h : IsPlaceOver A v}

def LocExt.fixSub (M : LocExt h) : Subgroup (Weil h) where
  carrier := {σ | ∀ z : M.L, (σ : G K Ω) (algebraMap M.L Ω z) = algebraMap M.L Ω z}
  one_mem' := fun _ => rfl
  mul_mem' := fun {σ τ} hσ hτ z => by
    show (σ : G K Ω) ((τ : G K Ω) _) = _
    rw [hτ z, hσ z]
  inv_mem' := fun {σ} hσ z => by
    show (σ : G K Ω).symm _ = _
    rw [AlgEquiv.symm_apply_eq, hσ z]

theorem LocExt.mem_fixSub (M : LocExt h) (σ : Weil h) :
    σ ∈ M.fixSub ↔ ∀ z : M.L, (σ : G K Ω) (algebraMap M.L Ω z) = algebraMap M.L Ω z := Iff.rfl

theorem LocExt.index_fixSub (M : LocExt h) : M.fixSub.index = Module.finrank K M.L :=
  EpsUnique.index_eq_finrank K M.L Ω A v h M.loc _ M.mem_fixSub

instance LocExt.finiteIndex_fixSub (M : LocExt h) : M.fixSub.FiniteIndex :=
  ⟨by rw [M.index_fixSub]; exact Module.finrank_pos.ne'⟩

variable {ψ : AddChar (v.adicCompletion K) Circle}

end Defs

end GlobalTheory.DelEps

end

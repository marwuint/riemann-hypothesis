import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Module

namespace GlobalTheory.WeilDeligne

section ProdLin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem inl_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace f r).map (LinearMap.inl ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := f) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inl ℂ V V')
    (fun x => Prod.ext rfl (map_zero g).symm) r

theorem inr_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace g r).map (LinearMap.inr ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := g) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inr ℂ V V')
    (fun x => Prod.ext (map_zero f).symm rfl) r

theorem mem_absSpace_prodMap (f : End ℂ V) (g : End ℂ V') (r : ℝ) (v : V × V') :
    v ∈ absSpace (f.prodMap g : End ℂ (V × V')) r ↔ v.1 ∈ absSpace f r ∧ v.2 ∈ absSpace g r := by
  constructor
  · intro hv
    exact ⟨map_absSpace_le (LinearMap.fst ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩,
      map_absSpace_le (LinearMap.snd ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (inl_absSpace_le f g r ⟨_, h1, rfl⟩) (inr_absSpace_le f g r ⟨_, h2, rfl⟩)

end ProdLin

end GlobalTheory.WeilDeligne

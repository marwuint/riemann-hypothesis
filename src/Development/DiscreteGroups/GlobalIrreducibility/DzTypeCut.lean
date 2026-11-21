import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LDepth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, ∀ τ : FDRep ℂ (Gn g n),
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥

end DiscreteGroups.sglob.DzType

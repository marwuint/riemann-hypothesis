import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.EqVolSDOf

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

def LevelIdeal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔪 𝔪' : Ideal (𝓞 E)) (M A : ℕ)
    (γ : Matrix (Fin N) (Fin N) E), IsLat Λ → 0 < M → 𝔪' * 𝔪 = Ideal.span {(M : 𝓞 E)} → (∀ x ∈ Λ, γ *ᵥ x ∈ Λ) →
    (((∀ x ∈ 𝔪 • Λ, ∃ e ∈ Λ, γ *ᵥ x = x + M • e) ∧ ∀ x ∈ Λ, ∃ e ∈ Λ, γ *ᵥ x = x + A • e) ↔
      ∀ x ∈ Λ, γ *ᵥ x - x ∈ (𝔪' ⊓ Ideal.span {(A : 𝓞 E)}) • Λ)

theorem neat_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {c : E ≃ₐ[F] E}
    {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) (hb : Neat c 𝔟) : Neat c 𝔞 := fun z h1 h2 => hb z h1 (h h2)

end PositivityTheory.EqVol

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

def FundFor (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ, ∀ b ∈ Bor X.Ψ r, cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

theorem fundFor_iff (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) :
    FundFor X X.Γ x0 FF ↔ IsFundSet X x0 FF := by
  exact Iff.rfl

end defs

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

end PositivityTheory.EqVol

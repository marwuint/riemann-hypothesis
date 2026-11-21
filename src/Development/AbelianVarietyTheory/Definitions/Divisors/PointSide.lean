import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

end Count

end GlobalTheory.LKCount

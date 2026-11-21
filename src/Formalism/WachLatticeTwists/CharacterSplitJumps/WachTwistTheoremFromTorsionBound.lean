import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheorem

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def StatCTBMono : Prop :=
  ∀ (ℓ s m e gK : ℕ) (U U' : Finset ℤ), U ⊆ U' → cTB ℓ s m e gK U ≤ cTB ℓ s m e gK U'

def HZeroInvariantsKilled : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] (G : Type) [Group G] (A : Type) [AddCommGroup A]
    [Module O A] (ρA : Representation O G A) (Dw : Subgroup G) (Dat : InvariantsCohomologyData ℓ) (b : Dat.M →+ A)
    (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ),
    (∀ z : A, (∀ g ∈ Dw, ρA g z = z) → ∃ x, b x = z) → HZeroHypotheses Dat w m U →
    ∀ z : A, (∀ g ∈ Dw, ρA g z = z) → ((ℓ : O) ^ c0 ℓ m U) • z = 0

def BKIn {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    {HV Cs HV' : Type}
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs) : Prop :=
  Module.Finite O Cs ∧
  (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) ∧
  (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) ∧
  (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) ∧
  (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) ∧
  F = ((HfV.restrictScalars O).map q).map Hc.subtype ∧ Fs = (HfV'.restrictScalars O).comap j'

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRowRhoNoBK (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (Hc : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    {Cs : Type*} [AddCommGroup Cs] [Module O Cs] (cls : (Dw → T₂) → Cs)
    (pr : Hc →ₗ[O] Cs →ₗ[O] KO O) (Fs Im : Submodule O Cs) : Prop :=
  ∃ (C₁ : (Dw → T₁) → Prop) (CN2 : (Dw → Dw → Ymod r χ E) → Prop)
    (CN : (Dw → Ymod r χ E) → Prop) (CA : (Dw → A) → Prop) (CP : (Dw → KO O) → Prop),
    (∀ a, C₁ a → CN2 (fun g h => inc (a g) • (uElt r χ (g : G) • yY r χ E (h : G)))) ∧
    (∀ a, C₁ a → CA (fun g => -(inc (a g) * (uElt r χ (g : G) * E)))) ∧
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) f, CN f → CP (fun g => ψ (f g))) ∧
    (∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), CN2 z →
      (∃ f, CA f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) ∧
    (∀ (a : Dw → T₁) (b : coZ1s (resRep (uRep O (M := M) r χ) Dw))
      (hb : Submodule.mkQ _ b ∈ Hc), a ∈ characterColumnKernelSet (resRep ρ₁ Dw) → C₁ a →
      (∃ c, CP c ∧ ∀ g h : Dw, γ (π (a g)) (uElt r χ (g : G) • (b : Dw → M) h) =
        ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) →
      pr ⟨Submodule.mkQ _ b, hb⟩ (cls (fun g => π (a g))) = 0) ∧
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet (resRep ρ₁ Dw), C₁ a ∧ x = cls (fun g => π (a g))) ∧
    Im ≤ Fs

def InRhoNoBK (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  (∀ l (x : Fin (j (colIdx l)) → KO O), (fun g : D (colIdx l) => ∑ a, tens (κ l a g) (x a)) ∈
    LinearMap.range (colDO (O := O) (M := M) r χ (D (colIdx l))) → ∀ a, x a = 0) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRhoNoBK M r χ E (D w) ε ρ₁ inc π γ (Hc w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

def StatInRhoBK : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    InRhoNoBK M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im →
    (∀ w ∈ what₂, F w = (annih (pr w) (Fs w)).map (Hc w).subtype) →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im

end Formalism.RepresentationBoundsCohomology.JT

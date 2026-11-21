import Formalism.WachLatticeTwists.SplitLocalLifts.StatCompColk

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRhoRest (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (what₂ : Finset ℕ) (s : ℕ∞)
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
  (∀ w ∈ what₂, InRowRho M r χ E (D w) ε ρ₁ inc π γ (Hc w) (F w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

end Formalism.RepresentationBoundsCohomology.JL

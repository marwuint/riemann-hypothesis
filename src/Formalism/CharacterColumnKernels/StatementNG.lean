import Formalism.CharacterColumnKernels.StatementN

open Finset

noncomputable section

namespace Formalism.NG

def LocalSubalgebraEtaBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
    ∀ B : X → ℕ∞, (∀ x ∈ Zg, vcc T (Z : Set X) x ≤ B x) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (B x + IsDiscreteValuationRing.addVal O (A : O))

end Formalism.NG

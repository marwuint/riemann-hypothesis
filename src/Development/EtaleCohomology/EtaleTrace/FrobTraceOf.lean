import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    pb l (f ≫ g) n = pb l f n ∘ₗ pb l g n := by
  unfold pb pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem gal_eq (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) : galHQ l Ω p n 0 σ = pb l (GlobalTheory.Et.galMap Ω p σ) n := rfl

end LateralTheory.EtaleTrace

end

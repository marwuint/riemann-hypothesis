import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts : Prop :=
  ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ),
    (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V),
    ∃ e : ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp ≅ (Arrow.mk (Ψ.map g).unop).cechNerve,
      lev Ψ (coAug g) = e.hom ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom


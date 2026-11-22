import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HostModel

open ToricData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelAgree {D : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k}
    (a : ArcIn D l (RingHom.id c.F) k bF) (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}))
    [Module (𝓞 E) P.toPre.X] {φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (uF : F),
    (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
    uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
    ∀ (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n),
      ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
        (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
      ∀ (q₀ : QkPt a.D₀ F n) (q₁ q₂ : QkPt P.toPre F n),
        QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
        (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        QkPt.Equiv P.toPre F q₁ q₂

variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)

def witP : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)

instance instModuleWitP : Module (𝓞 E) (witP c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))

end GlobalTheory.HostModel

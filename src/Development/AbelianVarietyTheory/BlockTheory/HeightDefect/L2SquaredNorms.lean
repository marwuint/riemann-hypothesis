import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Norms

variable {K₁ : Type} [Field K₁]

def hermSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  (z ⬝ᵥ Hm.mulVec (star z)).re

def IsL2SquareIntegralProblem (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (P.L.pull (eSec P.A))) (σ : K₁ →+* ℂ)
    (s : P.L.Sec) (v : ℝ) : Prop :=
  rig.IsGen ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (Fd : Set (Fin P.g → ℂ)),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    (∀ i : P.L.ι, ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i) →
      u.fr (fun _ => i) 0 =
        σ (valR (A := K₁) (𝟙 (Sp K₁)) ((P.L.pull (eSec P.A)).U (fun _ => i)) (rig.s (fun _ => i)).val)) ∧
    (∀ (i : P.L.ι) (z : Fin P.g → ℂ), ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valAt' ((u.ex z).left ≫ φ) (P.L.U i) (s.f i) = θ z * u.fr (fun _ => i) z) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧ volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
    IntegrableOn (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) Fd volume ∧
    v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) / (volume Fd).toReal

end Norms

end GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

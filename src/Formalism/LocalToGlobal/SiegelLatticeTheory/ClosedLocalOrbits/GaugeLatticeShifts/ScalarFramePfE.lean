import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfD

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

def IotaG (q : E) (abelian₂ : Submodule M.L.O V) {r : ℕ} (f₀ f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) : Prop :=
  (∀ x x' : V, x ∈ abelian₂ → x' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x' ∈ H.perp (H.X f₁) → x - x' ∈ H.smulLat q abelian₂ →
    ∃ y y'' : V, y ∈ abelian₂ ∧ y'' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y'' ∈ H.perp (H.X f₂) ∧ x - y ∈ H.X f₀ ∧
      e x' - y'' ∈ H.X f₂ ∧ y - y'' ∈ H.smulLat q abelian₂) ∧
  (∀ x x'' : V, x ∈ abelian₂ → x'' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x'' ∈ H.perp (H.X f₂) →
    x - x'' ∈ H.smulLat q abelian₂ →
    ∃ y y' : V, y ∈ abelian₂ ∧ y' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y' ∈ H.perp (H.X f₁) ∧ x - y ∈ H.X f₀ ∧
      e.symm x'' - y' ∈ H.X f₁ ∧ y - y' ∈ H.smulLat q abelian₂)

end Generic

end Formalism.L2.SG.Pf.ScalarFramePf

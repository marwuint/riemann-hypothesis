import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

noncomputable section

namespace Formalism.L2.PjFree.Rows

open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open MeasureTheory Formalism.L2.PjFree
open scoped Matrix

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

structure ModelsOf {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (r : ℕ) : Type 1 where
  X : Fin F.n → Data E r
  φ : ∀ i, (F.Di i).La ≃ₗ[𝓞 E] (X i).Λ

structure ModelBase {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) :
    Prop where
  rank : r = Dw.p + Dw.q
  type : ∀ k, (M.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k la γ, (M.X k).χ la γ = 1
  ef : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.φ k a : Fin r → E) (M.φ k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + (l.M : ℕ) • (M.φ k b : Fin r → E)) ∧
    ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) = (M.φ k a : Fin r → E) + (l.A : ℕ) • (M.φ k b : Fin r → E)
  domStab : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
    ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom

end Fam

end Formalism.L2.PjFree.Rows

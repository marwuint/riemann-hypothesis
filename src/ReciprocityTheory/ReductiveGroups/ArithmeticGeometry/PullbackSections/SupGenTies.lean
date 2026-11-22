import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def CuspTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → f ∈ T.C j w

structure XExt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : X.Ψ, ‖τ.1 X.ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ k : ℤ, EFf X.ξ0 X.Gm x y = k
  EF_perf : ∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ X.Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ X.Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ →
    (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ

def XExt.toX {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} (e : XExt X) :
    DataX E r :=
  ⟨X, e.k0, e.minWeight_pos, e.k0_le, e.ξ0_abs, e.EF_int, e.EF_perf, e.L', e.L'_fg, e.L'_int, e.L'_dual, e.NA, e.NC,
    e.NA_pos, e.NC_pos, e.NA_sub, e.NC_sub, e.g, e.g_pos, e.cong⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections

import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop} {C : PerC R}

structure XEnd (I : Iso l K C.K₀) : Type 2 where
  Ln : Model l K → Type 1
  oneT : ∀ M : Model l K, M.T 0 → Prop
  c1T : ∀ {M : Model l K}, Ln M → M.T 2 → Prop
  oneD : ∀ M : Model l K, I.D M 0 → Prop
  c1D : ∀ {M : Model l K}, Ln M → I.D M 2 → Prop
  cupD : ∀ (M : Model l K) (i j : ℕ), I.D M i →ₗ[C.K₀] I.D M j →ₗ[C.K₀] I.D M (i + j)

variable {I : Iso l K C.K₀}

structure CrysCmp.Plus (c : CrysCmp G C I) (X : XEnd I) (N : ℕ) : Prop where
  cup : ∀ (M : Model l K), G M → ∀ {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)), M.CupT x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i)) (b' : Module.Basis (Fin m') C.K₀ (I.D M j))
      (f : Module.Dual C.K₀ (I.D M (i + j))), c.c M (i + j) (M.toV _ z) f =
        ∑ s, ∑ s', c.c M i (M.toV _ x) (b.coord s) * c.c M j (M.toV _ y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
  one : ∀ (M : Model l K), G M → ∀ v y, X.oneT M v → X.oneD M y → ∀ f, c.c M 0 (M.toV 0 v) f = C.k (f y)
  c1 : ∀ (M : Model l K), G M → ∀ (L : X.Ln M) v y, X.c1T L v → X.c1D L y → ∀ f,
    (l : C.C) ^ N * C.c R.t * c.c M 2 (M.toV 2 v) f = C.k (f y)

end CrystallineSemistableComparison

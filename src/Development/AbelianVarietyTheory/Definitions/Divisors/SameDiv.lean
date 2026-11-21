import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

theorem SameDiv.symm {X : Scheme.{0}} {L M : LB X} {σ : L.Sec} {τ : M.Sec} (h : SameDiv σ τ) : SameDiv τ σ :=
  fun x => by
    obtain ⟨U, i, j, hi, hj, u, hx, e⟩ := h x
    exact ⟨U, j, i, hj, hi, u⁻¹, hx, by rw [e, Units.inv_mul_cancel_left]⟩

end GlobalTheory.LogPair

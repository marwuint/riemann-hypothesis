import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.TorusInvariantK0RegCusp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

section Y0

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

namespace ComponentData

variable (D : ComponentData Ψ K ι)

def cCoef (la : Ψ × Fin D.N → ℤ) (τ : Ψ) (r : Fin D.N) : ℤ :=
  if h : (r : ℕ) + 1 < D.N then la (τ, ⟨D.N - r - 1, by omega⟩) - la (τ, ⟨D.N - r - 2, by omega⟩)
  else -la (τ, ⟨0, by have := r.2; omega⟩)

def regWeight (la : Ψ × Fin D.N → ℤ) (t : ℝ) (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : ℝ :=
  ∑ x : Ψ × Fin D.N, (D.cCoef la x.1 x.2 : ℝ) * D.regFl t x.1 x.2 w

omit [DecidableEq Ψ] in
theorem j_le_N : D.j ≤ D.N := D.j_lt_N.le

end ComponentData

end Y0

section FlZ

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

variable {Ψ N}

end FlZ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

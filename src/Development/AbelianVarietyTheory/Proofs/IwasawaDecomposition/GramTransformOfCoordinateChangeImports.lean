import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData

set_option autoImplicit false

noncomputable section

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePairGram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def ent (M : Matrix (Fin r) (Fin r) ℂ) (a b : ℕ) : ℂ := if h : a < r ∧ b < r then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

open Classical in

def coef (X : Data E r) (x x' : Frame X.Ψ r) (ρ : E →+* ℂ) (b i : ℕ) : ℂ :=
  if h : ρ ∈ X.Ψ then ent ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) (X.p0 + b) (X.p0 + i)
  else if h' : conjEmb ρ ∈ X.Ψ then ent ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) (X.p0 - 1 - i) (X.p0 - 1 - b)
  else 0

end GlobalTheory.FramePairGram

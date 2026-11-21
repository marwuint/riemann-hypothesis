import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)

open Classical in

def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.TrueCx GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A)

abbrev cmAt (k : s.Comp) : D.what₂.Tau ≃ ((s.U κ.σ₀).X k).Ψ := cmEquiv _ s.isUnf L.ψ k

def bettiCo (k : s.Comp) (τ : D.what₂.Tau) (x : Frame ((s.U κ.σ₀).X k).Ψ N) : ℂ :=
  (hodgeC ((s.U κ.σ₀).X k) (cmAt s L k) τ : ℂ) ^ S.Dw.q * horizGen (cmAt s L k τ) x

abbrev detEx (S : Sig A N j) (τ : D.what₂.Tau) : Letter S.Dw → ℤ :=
  expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))

def IsBetti (k : s.Comp) (τ : D.what₂.Tau) (σ : (Φ.C k).Y.Fn) (b : ℂˣ) : Prop :=
  ∀ (x : ((s.U κ.σ₀).X k).dom) (a : ℂ),
    CoordAtC (Φ.C k) ((s.U κ.σ₀).un k x) (detEx S τ) σ a ↔ a = b * bettiCo s L k τ x.1

open Classical in

def flBetti (k : s.Comp) (τ : D.what₂.Tau) : ℂˣ :=
  if h : ∃ b, IsBetti s Φ L k τ (flatSec s Φ k τ) b then h.choose else 1

variable {s Φ L} {k : s.Comp} {τ : D.what₂.Tau} {σ : (Φ.C k).Y.Fn} {b b' : ℂˣ}

end GlobalTheory.ShFam.Pad

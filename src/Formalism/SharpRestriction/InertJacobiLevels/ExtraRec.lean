import Formalism.SharpRestriction.InertJacobiLevels.ExtraMods
import Formalism.LocalRingCardinality.SpanPowerMembership.TiesGen
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

def errXTw (X : ErrX D) (W : TwGap D) : ErrX (withTw D W) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong := X.piT_cong
  vPl := X.vPl
  vPl_inj := X.vPl_inj
  norm_mem_place_ideal := X.norm_mem_place_ideal

def LevGapD.withTw (G : LevGapD D) (W : TwGap D) : LevGapD (withTw D W) where
  lev := G.lev
  errX := errXTw G.errX W
  piG_lev := G.piG_lev
  piT_lev := G.piT_lev
  tau := G.tau
  tau_def := G.tau_def

section Rec

variable (D1 : D7) (W : TwGap D1) (large₂ : LevGapD D1) (h0 : ∀ u, Module.finrank ℂ (D1.mem u).A.Mu0 = 0)
  (rOf : D1.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (B : D1.what₂.Word → ℕ → Set (G.HH D1))

def recX : D7 := withGatCB (large₂.withTw W).recS h0 rOf eOf B

end Rec

end Formalism.MainNotions.Inhab

end

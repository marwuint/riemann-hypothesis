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

theorem recX_e (u w h) : ((recX D1 W large₂ h0 rOf eOf B).gat u w h).e = eOf (D1.what₂.places.resChar w) := rfl

def recX_X (S : Shape0 D1) : DivX (recX D1 W large₂ h0 rOf eOf B) := divXExample _ S.drows S.mj

theorem recX_kapR (S : Shape0 D1) (e) : (recX_X D1 W large₂ h0 rOf eOf B S).kapR e = 1 := rfl

theorem recX_h (u) : (recX D1 W large₂ h0 rOf eOf B).div.h u = D1.div.h u := rfl

set_option maxHeartbeats 2000000 in
theorem recX_hVal (sc : Scale) (aT : D1.host.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (recX D1 W large₂ h0 rOf eOf B) sc aT η Sc dl C u = hVal D1 sc aT η Sc dl C u := rfl

end Rec

end Formalism.MainNotions.Inhab

end

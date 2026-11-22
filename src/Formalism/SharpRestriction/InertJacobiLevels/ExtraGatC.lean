import Formalism.LocalRingCardinality.SpanPowerMembership.GatAdd
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

theorem two_ne_Kn (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (n : ℕ) : (2 : Kn p n) ≠ 0 := by
  intro h
  have h1 : ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 2 =
      ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 0 := by
    rw [map_ofNat, map_zero, h]
  have h2 : (2 : Wn p n) = 0 := inj_WK p n h1
  have h3 : ((2 : ℕ) : GaloisField p n) = 0 := by
    have := congrArg (WittVector.constantCoeff (p := p) (R := GaloisField p n)) h2
    rw [map_ofNat, map_zero] at this
    exact_mod_cast this
  have h4 := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

def gatOfC (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levAll _
    e := e }

theorem gatOfC_M (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : (gatOfC S T r lam comp e).M = ⊥ :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  gat_M_bot _ fun _ => levAll_M _ (two_ne_Kn p S.five_le _)

end One

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def withGatC : D7 :=
  { D with
    gat := fun u w h => gatOfC (served_of h) (bs u (D.what₂.places.resChar w))
      (rOf u (D.what₂.places.resChar w)) (fun ψ => (D.fm u).lam 0 (D.eTau.symm ψ)) ((D.mem u).C.cls 0)
      (eOf (D.what₂.places.resChar w))
    gat_d := fun u _ _ => (gat_d_zero _ (gatOfC_M _ _ _ _ _ _)).trans (h0 u).symm }

def gatTiesC : GatTies (withGatC D h0 rOf eOf bs) where
  gat_k := fun _ _ _ => k_pos D.R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ D.host _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u (D.what₂.places.resChar w))).trans D.eTau.symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ D.host _ (served_of h) (bs u (D.what₂.places.resChar w)) _ D.eTau v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (B : D.what₂.Word → ℕ → Set (HH D))

def withGatCB : D7 := withGatC D h0 rOf eOf (fun u p => tau1P D.R.toFrame '' B u p)

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

end Formalism.MainNotions.Inhab

end

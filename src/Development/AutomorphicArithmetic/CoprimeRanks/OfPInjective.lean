import Development.AutomorphicArithmetic.QuadraticCharacters.MemRealCyclotomicSubgroup
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

open Formalism.HC Formalism.FrobeniusOrbits

noncomputable section

namespace HostParam.Seam

structure FrameIso (C : Core) (φ : Frame) where
  iso : C.E.Gal ≃* φ.GG
  e_eq : φ.e = C.e
  ps_eq : ∀ g, φ.psC (iso g) = C.psG g
  ch_eq : ∀ g, φ.chC (iso g) = C.chG g
  conj_eq : iso C.E.conj = φ.cc
  iota_eq : iso C.iota = φ.iod
  A0_eq_image : ∀ g, g ∈ C.A0 ↔ ∃ s ∈ φ.A0, iso g = φ.tau1 s
  h_eq : ∀ (u : (ZMod C.E.N)ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod C.E.N).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (iso (C.E.res u)).2 = hcl φ.e v

structure Comparison₂ (C : Core) {φ : Frame} (H : HostRaw φ) extends FrameIso C φ where
  d_eq : H.d = C.d
  art_res : ∀ (a : ℕ) (h : a.Coprime C.E.N) (h' : a.Coprime H.condN),
    H.art (ZMod.unitOfCoprime a h') = iso (C.E.res (ZMod.unitOfCoprime a h))

structure AdmQ (C : Core) (q : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_split : SplitsIn C.d q
  q_inertia : Nat.card (C.E.inertia q) ≤ 2

structure admitted (C : Core) (q QS : ℕ) : Prop extends AdmQ C q where
  QS_pos : 0 < QS
  QS_coprime : Nat.Coprime QS (q * C.d)
  QS_split : ∀ l : ℕ, l.Prime → l ∣ QS → SplitsIn C.d l
  cond_dvd : C.E.conductor ∣ QS * q * C.d

def ofP (ψ : PChar) : PrimChar := ⟨ψ.N, ψ.χ⟩

def toP (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : PChar := @PChar.mk κ.1 ⟨h.ne'⟩ κ.2 hp

theorem ofP_toP (κ : PrimChar) (h : 0 < κ.1) (hp : κ.2.IsPrimitive) : ofP (toP κ h hp) = κ := rfl

theorem ofP_fst_pos (ψ : PChar) : 0 < (ofP ψ).1 := Nat.pos_of_ne_zero (NeZero.ne ψ.N)

theorem ofP_snd_isPrimitive (ψ : PChar) : (ofP ψ).2.IsPrimitive := ψ.prim

theorem toPrimitive_ofPrimitive (ψ : PChar) : toP (ofP ψ) (ofP_fst_pos ψ) (ofP_snd_isPrimitive ψ) = ψ := rfl

theorem ofP_of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ofP (PChar.of χ) = prim χ := rfl

theorem ofP_one : ofP PChar.one = ⟨1, 1⟩ := rfl

theorem ofP_inv (ψ : PChar) : ofP ψ.inv = ⟨(ofP ψ).1, (ofP ψ).2⁻¹⟩ := rfl

end HostParam.Seam

end

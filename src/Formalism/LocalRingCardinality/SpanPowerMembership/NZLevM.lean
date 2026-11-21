import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevL
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

theorem charZero_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    CharZero (Kn p (orderOf (gPsi S))) :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  charZero_of_setting (hidaSettingOfEven p _ S.five_le (ord_spec S).2.1 (ord_spec S).2.2)

theorem p_ne_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    ((p : ℕ) : Kn p (orderOf (gPsi S))) ≠ 0 :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  Nat.cast_ne_zero.mpr S.prime.ne_zero

def gatNZ (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levB (placesOf S T r lam) (p_ne_Kn S)
    e := e }

theorem gatNZ_eq (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    haveI := charZero_Kn S
    (gatNZ S T r lam comp e).M = (gatC (placesOf S T r lam) (p_ne_Kn S) comp).M := rfl

end One

variable (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂.NZ

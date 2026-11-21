import Formalism.CoboundaryTransfers.StatementAPI
import Formalism.WachModuleLifts.StatementW
import Formalism.LagrangeIdealLifts.Statement
import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section CLback

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

def toCL (B : Base ℤ_[p] A) (hp : B.p = p) (hq : B.QLin) (hφ : B.PhiX (p - 1)) :
    CL.W.Base p A where
  φA := B.φ
  γA := B.γ
  π₀ := B.X
  q := B.Q
  hq := by rw [hq, hp]; simp
  hφ := hφ
  comm := B.comm

def WachMod.toCL {B : Base ℤ_[p] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] (W : WachMod B M D) (hp : B.p = p)
    (hq : B.QLin) (hφ : B.PhiX (p - 1)) : CL.W.WachMod (toCL B hp hq hφ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  π₀_inj := W.X_inj
  q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_qN := W.γ_QN

end CLback

section LIFT

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]

variable {B : LIFT.Base ℓ A} {M : ℕ}

def toLIFT (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q)
    (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) : LIFT.Base ℓ A where
  φA := B.φ
  γA := B.γ
  X := B.X
  Q := B.Q
  u := u
  comm := B.comm
  φX := hφ
  γX := hγX
  γQ := by
    obtain ⟨v, hv, ⟨t, rfl⟩, hγ⟩ := hγQ
    exact ⟨t, hv, by rw [hγ, mul_comm]⟩

def WachMod.toLIFT {B : Base ℤ_[ℓ] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : WachMod B M D) (u : ℤ_[ℓ]ˣ)
    (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.WD (toLIFT B u hφ hγX hγQ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N

end LIFT

def baseOfArchimedeanComponents {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : WachCohomologyFacts.Base O A) :
    Base O A where
  p := B.ℓ
  hp := B.hℓ
  φ := B.φ
  γ := B.γ
  X := B.X
  Q := B.q
  comm := B.comm
  φX := ⟨B.u * (B.X + (B.ℓ : A)) ^ (B.ℓ - 1), by rw [B.hφX]; ring⟩

end Formalism.CoboundaryTransfers

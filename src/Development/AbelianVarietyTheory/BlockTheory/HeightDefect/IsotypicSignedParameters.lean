import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

structure SignedPar (n : ℕ) where
  lam : Fin n → ℝ
  sgn : Fin n → Bool
  hc : Formalism.QuantumDeterminants.IsHCParam lam

namespace SignedPar

variable {n : ℕ} (P : SignedPar n)

def p : ℕ := (Finset.univ.filter fun a => P.sgn a = true).card

def q : ℕ := (Finset.univ.filter fun a => P.sgn a = false).card

def IsOfSig (p q : ℕ) : Prop := P.p = p ∧ P.q = q

def low : Fin n → ℝ := Formalism.QuantumDeterminants.lowK P.sgn P.lam

end SignedPar

def IsFrame {n N : ℕ} (ε : Fin n → Bool) (G : Matrix (Fin N) (Fin N) ℂ) (A : Matrix (Fin n) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin n) ℂ) : Prop :=
  Aᴴ * Formalism.REAL.Jm ε * A = G ∧ A * B = 1 ∧ B * A = 1

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := V.gram.map (tauE D τ)

end Adelic

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsDSPar {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDS P.sgn P.lam σ

end Rep

end GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

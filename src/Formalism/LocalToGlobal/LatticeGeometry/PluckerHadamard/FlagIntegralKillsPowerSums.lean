import Formalism.WeightedDeltaMeans.LowerBoundLinearPower
import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology Finset

namespace Formalism.L2.Geo

section Alg

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def smallBlock (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => j ≤ i.val)

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def a0Mu (j : ℕ) : Pol Ψ N := ∑ τ : Ψ, ∑ i ∈ smallBlock N j, X (τ, i)

def blockVandermondePolynomial (τ : Ψ) (S : Finset (Fin N)) : Pol Ψ N :=
  ∏ a ∈ S, ∏ b ∈ S.filter (fun b => a < b), (X (τ, a) - X (τ, b))

def fibreVandermondeProduct (j : ℕ) (cf : ℝ) : Pol Ψ N :=
  C cf * ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j))

def a0JP (j n : ℕ) (cf : ℝ) : Pol Ψ N := a0Mu j ^ n * fibreVandermondeProduct j cf

def a0n (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

end Alg

section AlgStmt

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def FlagIntegralAnnihilatesPowerSums : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), Kills (degFlL Ψ N)

end AlgStmt

section Geo

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtensionData (U : ShimU D G jC ng w) where

  Xb : U.Comp → G.Var

  PtX : U.Comp → Type

  bdX : ∀ c, PtX c → Prop

  htX : ∀ c, G.Adl (Xb c) → PtX c → ℝ

  degX : ∀ c, G.Adl (Xb c) → ℝ

  semiposX : ∀ c, G.Adl (Xb c) → Prop
  nefFibX : ∀ c, G.Adl (Xb c) → Prop
  ampleX : ∀ c, G.Adl (Xb c) → Prop

  muC : ℝ → ℝ → ℝ → ∀ c, G.Adl (Xb c)

  arLim : ℝ → U.Comp → ℝ

  degMu : U.Comp → ℝ

  meanU : U.Comp → ℝ

  fdeg : ℝ

section Props

variable (U : ShimU D G jC ng w) (X : ExtensionData U)

abbrev nA (w : Dat D Lev) : ℕ := a0n D.what₂.Tau w.N w.j

def JA (w : Dat D Lev) (cf : ℝ) : ℝ := by
  classical
  exact degFlL D.what₂.Tau w.N (a0JP w.j (nA w) cf)

end Props

end Geo

end Formalism.L2.Geo

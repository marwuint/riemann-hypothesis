import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

open MvPolynomial Filter Topology
open scoped Classical

noncomputable section

structure Shape where

  f : ℕ

  N : ℕ

  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N
  two_lt : 2 < f * (N - 1)

namespace Shape

variable (S : Shape)

abbrev Var : Type := Fin S.f × Fin S.N

abbrev Poly : Type := MvPolynomial S.Var ℝ

abbrev Emb : Type := Fin S.f × Bool

def D : ℕ := S.f * (S.N * (S.N - 1) / 2)

def top : Finset (Fin S.N) := Finset.univ.filter (fun i => (i : ℕ) < S.j)

def bot : Finset (Fin S.N) := Finset.univ.filter (fun i => S.j ≤ (i : ℕ))

def rho : S.Var →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => (v.2 : ℕ))

def permVar (w : Fin S.f → Equiv.Perm (Fin S.N)) : S.Var ≃ S.Var :=
  Equiv.prodShear (Equiv.refl _) w

def sgn (w : Fin S.f → Equiv.Perm (Fin S.N)) : ℝ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤ) : ℝ)

def intFl : S.Poly →ₗ[ℝ] ℝ :=
  ∑ w : Fin S.f → Equiv.Perm (Fin S.N),
    S.sgn w • ((lcoeff ℝ S.rho) ∘ₗ (rename (S.permVar w)).toLinearMap)

def linForm (u : S.Var → ℝ) : S.Poly := ∑ v, C (u v) * X v

def degU (u : S.Var → ℝ) : ℝ := S.intFl ((-S.linForm u) ^ S.D)

def maxAbs (u : S.Var → ℝ) : ℝ := ⨆ v, |u v|

def B0 (u : S.Var → ℝ) (g : ℝ) : ℝ := 4 * S.f * S.N ^ 2 * (1 + S.maxAbs u / g)

end Shape

open Shape

structure HostPrimes (S : Shape) where

  badNum : ℕ
  badNum_pos : 0 < badNum
  two_dvd_badNum : 2 ∣ badNum

  splits : ℕ → Bool

  frob : ℕ → Equiv.Perm S.Emb
  frob_conj : ∀ p (σ : S.Emb), frob p (σ.1, !σ.2) = ((frob p σ).1, !(frob p σ).2)
  frob_split : ∀ p (σ : S.Emb), p.Prime → ¬ p ∣ badNum → splits p = true →
    (frob p σ).2 = σ.2
  frob_inert : ∀ p (σ : S.Emb), p.Prime → ¬ p ∣ badNum → splits p = false →
    (frob p σ).2 = !σ.2

namespace HostPrimes

variable {S : Shape} (H : HostPrimes S)

def good (p : ℕ) : Prop := p.Prime ∧ ¬ p ∣ H.badNum

end HostPrimes

structure EndData (S : Shape) extends HostPrimes S where

  vol : ℝ
  vol_pos : 0 < vol

  PP : ℕ → S.Poly →ₗ[ℝ] ℝ

  hh : S.Poly →ₗ[ℝ] ℝ

  delta : ℕ → S.Poly →ₗ[ℝ] ℝ

  al : ℕ → Fin S.f → ℝ

  be : ℕ → Fin S.f → ℝ

  alM : ℕ → ℝ

  beM : ℕ → ℝ

  EE : ℕ → S.Poly →ₗ[ℝ] ℝ

  B1 : ℕ

  rd : ℝ
  one_le_rd : 1 ≤ rd

  LK : ℝ
  LK_nonneg : 0 ≤ LK

namespace EndData

variable {S : Shape} (V : EndData S)

def goodIoc (B0 B : ℕ) : Finset ℕ := (Finset.Ioc B0 B).filter V.good

def aB (B0 : ℕ) (B : ℕ) : ℝ :=
  V.alM B - V.beM B + ∑ p ∈ V.goodIoc B0 B, Real.log p / ((p : ℝ) - 1)

end EndData

namespace Shape

variable (S : Shape)

def kap (u : S.Var → ℝ) (Q : Fin S.N → Fin S.f → S.Poly) (k : Fin S.N) (τ : Fin S.f)
    (γ : S.Poly) : ℝ :=
  (((k : ℕ) + 1 : ℕ) : ℝ) * S.intFl (γ * Q k τ) / (((S.D + 1 : ℕ) : ℝ) * S.degU u)

end Shape

structure LimitData (S : Shape) where

  Mbar : (S.Var → ℝ) → ℚ → ℝ

  Ps : (S.Var → ℝ) → ℝ → ℝ

  shift : S.Var → ℝ

namespace LimitData

end LimitData

open EndData HostPrimes LimitData

def Shape.ex : Shape := ⟨3, 2, 1, le_refl _, le_refl _, by norm_num, by norm_num⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

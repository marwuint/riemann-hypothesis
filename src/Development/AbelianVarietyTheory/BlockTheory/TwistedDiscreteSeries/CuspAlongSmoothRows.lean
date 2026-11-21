import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

variable {D : D7}

variable (D) in

def Sizes : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

section Arrow

variable (θ : InfFam D)

def IsCuspOfType (N : Node D) (φ : GA D N.V → ℂ) : Prop :=
  IsAutFunSm θ N.V φ ∧ IsCuspFun N.V φ ∧ ∀ τ, IsTypeAt θ N.V τ (N.S τ) φ

variable {A B : Node D} {P : Type} (m : A.MeasDat)

def LiftsMult (K : P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M) : Prop :=
  ∀ F ∈ A.Cusp θ, ∃ F' ∈ B.Cusp θ, ∀ (p : P) (v : SmT A.M) (h : GA D B.V),
    IntegrableOn (fun g => K p h g * F v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F v g ∂m.ν = F' (It p v) h

def LiftsSmooth (K : GA D B.V → GA D A.V → ℂ) : Prop :=
  ∀ φ, IsCuspOfType θ A φ → (∀ h, IntegrableOn (fun g => K h g * φ g) m.fd m.ν) ∧
    IsCuspOfType θ B fun h => ∫ g in m.fd, K h g * φ g ∂m.ν

end Arrow

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure RowBase : Prop where

  lev : R.toLevCh.Is A.μ0

  inf : IsInfFam R.θ

  measY : R.models_νY

  measY' : R.models_νY'

  measX : R.models_νX

variable {R}

variable (G : GridPre R)

structure CuspAlong : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    LiftsMult R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j)
      (fun p h g => thetaKO (G.X i j).ω h g (fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f p)) fun p v => (G.X i j).It p v

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    LiftsMult R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1))
      (fun p h g => thetaKO (G.th t i j).ω h g (fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f p)) fun p v => (G.th t i j).It p v

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i)
      (fun p h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p))) fun p v => G.ItU i p v

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1))
      (fun p h g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p)) fun p v => (G.dn i).It p v

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    LiftsMult R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j)
      (fun p h g => thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f p)) fun p v => (G.col t j).It p v

structure CuspAlongSmooth : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.V (i + 1) j).V) (G.V i j).V Φ →
    LiftsSmooth R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j) fun h g => thetaKO (G.X i j).ω h g Φ

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1)) fun h g => thetaKO (G.th t i j).ω h g Φ

  up : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i) fun h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)

  dn : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1)) fun h g => thetaKO (G.dn i).ω g h Φ

  col : ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j) fun h g => thetaKO (G.col t j).ω g h Φ

end Grid

def LiftsCuspidalAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlong G

def LiftsCuspidal : Prop := ∀ D : D7, LiftsCuspidalAt D

def LiftsCuspidalSmoothAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlongSmooth G

end GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

end

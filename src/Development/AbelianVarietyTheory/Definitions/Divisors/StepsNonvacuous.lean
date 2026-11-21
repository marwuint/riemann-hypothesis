import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

abbrev jet {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) : J.B := taylor (n + 1) J.t f

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E} {n : ℕ}
  {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n}

structure Germ (Y : Family J T.X T.δ T.low) : Type 1 where

  B : Type
  [cr : CommRing B]
  [alg : Algebra ℂ B]
  smooth : Algebra.Smooth ℂ B

  X : Obj (FR E) 𝔠 (Sp B)

  δ : X.DetGen

  j : B →ₐ[ℂ] J.B

  q : Y.X'.A.left ⟶ X.A.left
  pull : Y.X'.IsPullBy X (spMap (j : B →+* J.B)) q

  δ'' : Y.X'.DetGen
  corr : Obj.DetCorr (j : B →+* J.B) q δ.1 δ''.1

  e : J.B
  he : Y.δ'.1 = e • δ''.1

  U : Set (I → ℂ)
  isOpen : IsOpen U
  zero : 0 ∈ U

  y : (I → ℂ) → (B →ₐ[ℂ] ℂ)
  hol : ∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U
  jet_eq : ∀ b, j b = jet J fun z ↦ y z b

attribute [instance] Germ.cr Germ.alg

structure Coord (ε : ℤˣ) {Y : Family J T.X T.δ T.low} (G : Germ Y) : Type 1 where

  V : Set (I → ℂ)
  isOpen : IsOpen V
  zero : 0 ∈ V
  sub : V ⊆ G.U

  X : (I → ℂ) → Obj (FR E) 𝔠 (Sp ℂ)

  q : ∀ z, (X z).A.left ⟶ G.X.A.left
  pull : ∀ z, (X z).IsPullBy G.X (spMap (G.y z : G.B →+* ℂ)) (q z)
  mor : ∀ z, GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 ℂ) (𝟙 _) (X z).A (G.y z : G.B →+* ℂ) (spMap (G.y z : G.B →+* ℂ)) (q z)

  δ : ∀ z, (X z).DetGen
  corr : ∀ z, Obj.DetCorr (G.y z : G.B →+* ℂ) (q z) G.δ.1 (δ z).1

  ζ : (I → ℂ) → I → ℂ
  ζ_hol : DifferentiableOn ℂ ζ V
  ζ_zero : ζ 0 = 0
  ζ_mem : ∀ z ∈ V, ζ z ∈ polydisc I

  U : ∀ z ∈ V, Unif φ L (ζ z) (X z)
  e_eq : ∀ z hz, (U z hz).e = T.U.e

  C : (I → ℂ) → ℂ
  det : ∀ z hz, (U z hz).IsDet (δ z).1 (C z)

  P₀ : T.U.u.Λ →+ HdR T.X.A
  per : IsPeriodMap ε T.U.u P₀

  P : ∀ z, T.U.u.Λ →+ HdR (X z).A
  lie : ∀ z hz (x : T.U.u.Λ), ∃ v, IsLieImage (P z x) v ∧
    (U z hz).u.IsDiff (fun a ↦ x.1 a + ζ z (T.U.e a) * starRingEnd ℂ (x.1 a)) v
  P_hol : ∀ x (c : primDR G.X.A), DifferentiableOn ℂ (fun z ↦ P z x ((mor z).pull c)) V
  horiz : ∀ (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    (x : T.U.u.Λ) (d : Crys J.κ (spMap J.π) T.X.A), Y.mor.Corr (P₀ x) d → ∀ c : primDR G.X.A,
    crysToDR J.κ Y.pull.grp d (m'.pull c) = jet J fun z ↦ P z x ((mor z).pull c)

def JetCalc : Prop :=
  ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n),
    (∀ f, AnalyticAt ℂ f 0 → ∀ (ν : Idx I n) (u : List I), (∀ i, u.count i = ν.1 i) → J.b.repr (jet J f) ν = iterD u f 0) ∧
    (∀ f g, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → jet J (f * g) = jet J f * jet J g ∧ jet J (f + g) = jet J f + jet J g) ∧
    (∀ f g, f =ᶠ[𝓝 0] g → jet J f = jet J g) ∧ (∀ a : ℂ, jet J (fun _ ↦ a) = algebraMap ℂ J.B a) ∧
    (∀ i, jet J (fun z ↦ z i) = J.t i) ∧ (∀ i, J.π (J.t i) = 0) ∧ ∀ s : Fin (n + 1 + 1) → I, ∏ a, J.t (s a) = 0

namespace Check

end Check

end GlobalTheory.LatJet.An

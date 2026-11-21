import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points
open GlobalTheory.GradedPieces IsLocalRing

namespace GlobalTheory.LocM.FJ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Value

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure GrTriv (Z : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (F : Z.X.Modules) : Type 1 where

  L : LB Z.X

  isLB : L.IsLB

  hU : ∀ i, IsAffineOpen (L.U i)

  w : ∀ i, Vecs Dw (Y Z.i).t Γ(Z.X, L.U i)

  int : ∀ i, IntFrame Z (hU i) (w i)

  trans : ∀ (i i' : L.ι) (k : Type) [Field k] (φ : Γ(Z.X, L.U i) →+* k) (φ' : Γ(Z.X, L.U i') →+* k)
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (hU i).fromSpec = spMap φ' ≫ (hU i').fromSpec → Set.range (spMap φ ≫ (hU i).fromSpec) ⊆ Z.opn →
    (∀ σ, DiagAt (Y Z.i).t (spMap φ ≫ (hU i).fromSpec ≫ Z.π) ((w i').bc φ' σ) ((w i).bc φ σ) (d σ)) →
    valR (spMap φ ≫ (hU i).fromSpec) _ (L.g i i').val = ∏ σ, ∏ a, d σ a ^ e σ a

  iso : F ≅ GlobalTheory.LB.toMod L

variable {Z : Mdl Y i₀} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}

variable {F : Z.X.Modules} (T : GrTriv Z e F) {V : Z.X.Opens} {k : Type} [Field k]

end Value

end GlobalTheory.LocM.FJ

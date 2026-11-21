import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain.CanTens

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k}

theorem presents_dual {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (-D) (CechPic.dual L) fun i => (r i)⁻¹ := by
  refine ⟨isLB_dual h.isLB, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  change (((r i)⁻¹ : X.functionFieldˣ) : X.functionField) =
    fnOf (L.U i ⊓ L.U j) hij ((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) * ((r j)⁻¹ : X.functionFieldˣ)
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, h.isRatSec i j hij, mul_inv]

end GlobalTheory.LatChain.CanTens

end

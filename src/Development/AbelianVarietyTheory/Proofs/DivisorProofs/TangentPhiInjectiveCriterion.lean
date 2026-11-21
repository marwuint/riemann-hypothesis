import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt.CnSurj

theorem kappa_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (r : Γ(Sp O, ⊤))
    (s : Γ(GlobalTheory.Conormal.conormal (GlobalTheory.LieVB.sec (zeroSec O M)), ⊤)) :
    kappa O M (r • s) = toO O r • kappa O M s := by
  letI := (isChart O M).algebra
  letI := topModule O M
  exact map_smul ((AugCot.lift ((isChart O M).aug (GlobalTheory.LieVB.sec_hom _)) (sndFn O M)
    (sndFn_der O M)) ∘ₗ ((isChart O M).augCotEquiv (GlobalTheory.LieVB.sec_hom _)).symm.toLinearMap) r s

theorem Phi_smul {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]
    (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w := by
  have e : toO O (GlobalTheory.LieVB.cst O c) = c := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c
  have h1 := map_smul (QCoh.appLinear (GlobalTheory.LieVB.cotMap z h) ⊤) (GlobalTheory.LieVB.cst O c)
    (show Γ(GlobalTheory.LieVB.omega A, ⊤) from w)
  refine (congrArg (kappa O M) h1).trans ((kappa_smul O M _ _).trans ?_)
  rw [e]
  rfl

end GlobalTheory.SqZeroPt.CnSurj

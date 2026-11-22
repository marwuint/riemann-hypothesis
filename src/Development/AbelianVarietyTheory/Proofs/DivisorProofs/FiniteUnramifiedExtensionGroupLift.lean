import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem root_congr {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} {t t' : T ⟶ S} (e : t = t')
    (h : Root A P t) : Root A P t' := e ▸ h

theorem residue_lift (R R' k'' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Field k''] [Algebra (ResidueField R) k'']
    (ε : ResidueField R ⊗[R] R' ≃ₐ[ResidueField R] k'') :
    ∃ φ : k'' →+* ResidueField R', φ.comp (algebraMap (ResidueField R) k'') =
      algebraMap (ResidueField R) (ResidueField R') := by
  let g₂ : ResidueField R ⊗[R] R' →ₐ[ResidueField R] ResidueField R' :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  refine ⟨(g₂.comp ε.symm.toAlgHom).toRingHom, ?_⟩
  ext a
  exact (g₂.comp ε.symm.toAlgHom).commutes a

end GlobalTheory.PolBundleLoc

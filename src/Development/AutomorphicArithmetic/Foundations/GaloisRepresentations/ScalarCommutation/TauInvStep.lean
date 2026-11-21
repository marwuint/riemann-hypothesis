import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
import Development.AutomorphicArithmetic.IwahoriCommensurability.AffineWeylSimpleReflectionCoset

set_option autoImplicit false

noncomputable section

open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

namespace UpperTheory.Gal.Spc.Iw

private def LI {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop :=
  ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K g) = dosetInd ℂ K 1

private def Qr {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop := ∀ h, LI K h → LI K (h * g)

private theorem Qr.mul {G : Type} [Group G] {K : Subgroup G} {g g' : G} (a : Qr K g) (b : Qr K g') : Qr K (g * g') :=
  fun h hh => by simpa [mul_assoc] using b _ (a h hh)

end UpperTheory.Gal.Spc.Iw

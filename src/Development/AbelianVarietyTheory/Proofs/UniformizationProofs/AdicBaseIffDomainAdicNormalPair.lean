import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RawDegreeForms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegCompare

open GlobalTheory.PsiInPull GlobalTheory.PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def toRaw (D : DegPre R) : IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg R where
  P := D.P
  rig := D.rig
  rig_gen := D.rig_gen
  cube := D.cub
  sym := D.sym
  sym_gen := D.sym_gen
  sym_rig := D.sym_rig
  X := D.X
  c := D.c
  c_add := D.c_add
  ψ := D.psi
  ψ_gen := D.psi_gen

variable (D : DegPre R)

section Values

variable {D} {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_tau (a b : D.X) : val (D.tau a b) r z J =
    val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_tau_symm (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  rw [val_tau r hJ, val_tau r hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

end Values

theorem psiEven_iff : D.PsiEven ↔ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).ψ (-χ))
      (LB.pullGen D.P.L (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.symφ D.P.A) IndefiniteRowSideFullHecke.CompleteLocalNormalRings.symε (toRaw D).sym ((toRaw D).cK χ).left))
    ((toRaw D).ψ χ) := Iff.rfl

end GlobalTheory.DegCompare

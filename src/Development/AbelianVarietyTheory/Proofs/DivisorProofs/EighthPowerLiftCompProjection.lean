import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfPowQuotient

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

end GlobalTheory.Mum.Pow8

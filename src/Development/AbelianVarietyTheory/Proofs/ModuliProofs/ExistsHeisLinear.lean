import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

structure Change (S : ThetaSys o Ω) where
  J : Type
  [fin : Fintype J]
  [ne : Nonempty J]
  M : Matrix S.J J o
  M' : Matrix J S.J o
  mul_inv : M * M' = 1
  inv_mul : M' * M = 1
  e : S.Gam → ℕ

attribute [instance] Change.fin Change.ne

theorem zeta_ne_zero (S : ThetaSys o Ω) (e : ℕ) : algebraMap o Ω (S.ζ ^ e) ≠ 0 :=
  (((S.prim.isUnit (level_ne_zero S)).pow e).map _).ne_zero

def change (S : ThetaSys o Ω) (c : Change S) : ThetaSys o Ω :=
  { S with
    J := c.J
    fin := c.fin
    ne := c.ne
    ρ := fun a => c.M' * S.ρ a * c.M
    ρ_one := fun a h => by rw [S.ρ_one a h, Matrix.mul_one, c.inv_mul]
    ρ_mul := fun a b => (S.ρ_mul a b).imp fun k hk => by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    ρ_add := fun a b h => by
      rw [← S.ρ_add a b h]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc c.M, c.mul_inv, Matrix.one_mul]
    th := fun a => algebraMap o Ω (S.ζ ^ c.e a) * S.th a
    ev := fun a j => ∑ i, algebraMap o Ω (c.M i j) * S.ev a i
    th_mem := fun a => mul_mem (S.R.algebraMap_mem _) (S.th_mem a)
    ev_mem := fun a j => sum_mem fun i _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem a i)
    supp := by
      rw [← S.supp]
      congr 1
      ext a
      simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, zeta_ne_zero S, false_or]
    th_ne := S.th_ne.imp fun a h => mul_ne_zero (zeta_ne_zero S _) h }

def Change.inv {S : ThetaSys o Ω} (c : Change S) : Change (change S c) where
  J := S.J
  M := c.M'
  M' := c.M
  mul_inv := c.inv_mul
  inv_mul := c.mul_inv
  e := fun a => ((S.r * S.N) ^ 2 - 1) * c.e a

end GlobalTheory.RealCompare
end

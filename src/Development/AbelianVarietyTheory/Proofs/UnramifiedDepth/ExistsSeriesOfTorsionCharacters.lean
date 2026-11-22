import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharGerm

section Value

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

lemma comp_χ_of_le {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  induction n, h using Nat.le_induction with
  | base => rw [torsion_hom_ext huv]
  | succ n hmn ih =>
    have h1 : (u ≫ torsion.ι G (p ^ m)) ^ (p ^ n) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, pow_mul, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, one_pow]
    rw [ih (torsionLift _ h1) (torsionLift_ι _ _).symm]
    exact χ.compat n _ _ _ (by rw [torsionLift_ι, huv])

lemma comp_χ_eq {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm

end Value

end CharGerm

end GlobalTheory

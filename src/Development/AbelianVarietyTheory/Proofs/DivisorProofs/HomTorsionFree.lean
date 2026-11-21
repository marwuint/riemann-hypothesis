import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_torsionFree : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  intro K _ A B n f hn h
  have hs := (_root_.GlobalTheory.MulIsogeny.mul_isogeny K A n hn).1.2
  refine _root_.GlobalTheory.AV.AbVar.cancel_of_surjective K A A (n • 𝟙 A) hs B f 0 ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, Limits.comp_zero, h]

end GlobalTheory.AV.AbVar

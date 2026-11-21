import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs

open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

end GlobalTheory.UnitDeterminantBasis

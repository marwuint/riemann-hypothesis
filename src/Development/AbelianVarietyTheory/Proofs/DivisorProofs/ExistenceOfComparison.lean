import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_ext_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C ℝ≥0) (hv : v.Integers O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral) (j0 : A →+* O)
    (hj0 : Function.Injective ((algebraMap O C).comp j0)) :
    ∃ j1 : B →+* O, j1.comp φ = j0 ∧ Function.Injective ((algebraMap O C).comp j1) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A O := j0.toAlgebra
  letI : Algebra A C := ((algebraMap O C).comp j0).toAlgebra
  haveI : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hφ
  haveI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).2 hj0
  let ψ : B →ₐ[A] C := IsAlgClosed.lift
  have hmem : ∀ b : B, ∃ o : O, algebraMap O C o = ψ b := fun b => by
    have h1 : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral (R := A) b).map ψ
    have h2 : IsIntegral O (ψ b) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose f hf using hmem
  have hinj := hv.hom_inj
  let j1 : B →+* O :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add, hf, hf, hf, map_add]) }
  have hcomp : j1.comp φ = j0 := by
    ext a
    apply hinj
    change algebraMap O C (f (algebraMap A B a)) = algebraMap A C a
    rw [hf, ψ.commutes]
  refine ⟨j1, hcomp, ?_⟩
  have hψ : (algebraMap O C).comp j1 = ψ.toRingHom := RingHom.ext fun b => hf b
  rw [hψ, RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  have : ψ.toRingHom.comp (algebraMap A B) = algebraMap A C := ψ.comp_algebraMap
  rw [this]
  exact hj0

end GlobalTheory.FlatModel

end

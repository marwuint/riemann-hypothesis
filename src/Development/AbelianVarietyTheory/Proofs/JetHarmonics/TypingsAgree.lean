import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

open QForm in

theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

end GlobalTheory.TorsionFactsCompare

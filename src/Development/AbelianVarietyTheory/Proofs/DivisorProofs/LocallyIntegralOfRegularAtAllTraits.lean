import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := _root_.GlobalTheory.Mum.intAt_closed_of_traitReg R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := _root_.GlobalTheory.Mum.intAt_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact _root_.GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart R M G hsm Y α t hpb W U hWU hWa hUa _
    (_root_.GlobalTheory.Mum.chartVal_isIntegral_of_intAt L α k s j W hW hWa (_root_.GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum

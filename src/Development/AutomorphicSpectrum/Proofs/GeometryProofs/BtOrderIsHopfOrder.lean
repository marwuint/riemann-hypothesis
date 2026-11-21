import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import GroundTheory.PAdicHodge.FiniteFlat
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [_root_.GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (_root_.GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact _root_.GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder R T H H.subtype H.subtype_injective A hA

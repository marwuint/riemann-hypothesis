import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import GroundTheory.PAdicHodge.FiniteFlat
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtHopf
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProper
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨_root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ, ?_,
    fun hN => _root_.GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale R T Γ
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => _root_.GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R T Γ
    obtain ⟨hoi, htr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite R T Γ j hj
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion R T Γ S G x N i hi a
    refine _root_.GlobalTheory.CompanionTheory.Ar.BT.Funct.comp_mem_btOrder R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change R T R' _
      (_root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneCosetBF : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf
  refine ⟨_root_.GlobalTheory.FinPl.VacFlat.flat_vac D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf, ?_⟩
  intro h hh hne
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    _root_.GlobalTheory.IwaPlace.iwasawa_at_place D J.W J.W₀ ρ J.d LW LW₀ v hG.tame hG.sdW hG.sdW₀ hG.monoW h hh
  have h1 := _root_.GlobalTheory.FinPl.oneBF_red_torus D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have hinv := _root_.GlobalTheory.FinPl.InvStep.inv_int D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hrat := _root_.GlobalTheory.FinPl.RatioStep.ratio_int D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hlast := _root_.GlobalTheory.FinPl.LastDiag.last_diag_int D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hint := _root_.GlobalTheory.FinPl.DiagInt.diag_int D ρ v t ht hinv hrat hlast
  have hK := _root_.GlobalTheory.FinPl.LeviUnitK.inK_levi D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * J.d.emb0 γ, ?_, ?_, J.d.levi t * κ, GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem D J.W LW (· = v) _ _ hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  · exact Subgroup.mul_mem _ hnG (_root_.GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup D J.W J.W₀ ρ J.d (· = v) γ hγ)
  · rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MemMatch

variable {D : D7}

theorem st_of_kset (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) (hκ : (iotaX X h κ).2 ∈ X.B.I.Kset) : Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset → Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI hx
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx' := (GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) _).1 hx
    rw [e2]
    exact hx'
  exact key X.B.I h hκ

theorem exists_generic (Pg : Finset (Pl D.host.E)) : ∃ ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ := by
  have h : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ hψ using h
  exact ⟨ψ, fun PP _ => hψ PP⟩

theorem isIdentityOffFreePositions_rightBlock_iff {K : Type} [CommRing K] {r n : ℕ} (ρ k : ℕ) (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) K) :
    GlobalTheory.SymRes.IsPat ρ k (upperLeftBlock hr g) ↔ GlobalTheory.SymRes.IsPat ρ k g := by
  obtain rfl : r = n := le_antisymm hr hn
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]

theorem reductionBlock_injective_of_eq {K : Type} [CommRing K] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g g' : GL (Fin n) K)
    (h : upperLeftBlock hr g = upperLeftBlock hr g') : g = g' := by
  obtain rfl : r = n := le_antisymm hr hn
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem conj_mem_GfC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (s k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0)) : s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := by
  rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h] at hk ⊢
  rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]

theorem exists_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hTP : IsTypePlaces Pg) (hsp : ∃ e, IsIdemSum e Pg)
    (hid : ∀ PP : Pg, ∃ e, Formalism.L2.NTheta.IsIdemAt (D := D) e PP.1)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (Λ) (N : ℕ) (hβ : Lev.IsBaseFrame (D.sp.Y 0) β Λ N) (s : GA D (D.sp.Y 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) :
    ∃ m : ∀ PP : Pg, GL (Fin (D.sp.Y 0).rank) (kP PP.1), ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β →
      ((iotaX X h (s * k * s⁻¹)).2 ∈ X.K2 ↔ ∀ PP : Pg, m PP * redFn β PP.1 (finE (D.sp.Y 0) k) * (m PP)⁻¹ ∈
        unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k) := by
  obtain ⟨ψ0, hψ⟩ := exists_generic Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hTP (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hTP hsp) ψ0 hψ
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  obtain ⟨β₂, rfl⟩ : ∃ β₂, β₀ = finE (D.sp.Y 0) s * β₂ := ⟨(finE (D.sp.Y 0) s)⁻¹ * β₀, by group⟩
  have h12 : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β → finE (D.sp.Y 0) k ∈ St β₂ := by
    intro k hk hS
    have h1 := ((hSt (s * k * s⁻¹)).1 ⟨conj_mem_GfC X h s k hk, by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hS⟩).2
    have h2 := st_of_kset X h _ hβ₀ _ h1
    rwa [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at h2
  have hm := fun PP : Pg => (hid PP).elim fun e he => _root_.GlobalTheory.NestedStab.redFn_conj_of_stab_le D (D.sp.Y 0) β β₂ Λ N hβ e PP.1 he h12
  choose m hm using hm
  refine ⟨m, fun k hk hS => ?_⟩
  rw [(hK _).1, hfe, GlobalTheory.FrameConj.conj_mem_St_iff]
  simp only [GlobalTheory.FrameConj.redFn_conj]
  refine ⟨fun hh PP => ?_, fun hh => ⟨h12 k hk hS, fun PP hPP => ?_⟩⟩
  · rw [← hm PP _ hS (h12 k hk hS)]; exact hh.2 PP.1 PP.2
  · rw [hm ⟨PP, hPP⟩ _ hS (h12 k hk hS)]; exact hh ⟨PP, hPP⟩

end GlobalTheory.MemMatch

end

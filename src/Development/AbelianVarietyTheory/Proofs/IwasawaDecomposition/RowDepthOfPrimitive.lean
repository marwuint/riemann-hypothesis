import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemIsot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowDepthTrue

set_option maxHeartbeats 1000000 in

theorem rowDepth_rowRepR : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → D.host.F = maximalRealSubfield D.host.E →
    GlobalTheory.HeightCounting.RowDepth D (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHo hF σ k v
  obtain ⟨s, hs⟩ := GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D k v
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHo hF σ s
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hA⟩ := GlobalTheory.RowLevelSplit.lemA_pf
    (GlobalTheory.RowLevelSplit.stdFrame_splitPlace_entries_off_place GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one GlobalTheory.ConjLt.frame_mat_sub_one_lt GlobalTheory.SplitFrameW.main
      GlobalTheory.PlaceOverSplit.eq_or_eq_cP) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _ Y.stdPsi.1 hβ s
  have hh : ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ →
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧
        levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
    intro b κ hκ hk
    classical
    exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left
      Finset.subset_union_right (Y.PY.into κ) (hA κ hκ hk _)
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.RowFix.exists_fixed_rowRep D (Yc D 0) D.R.r _ R.θ Y.PY (R.MY 0) _ _ _ (Y.eFT σ)
    (fun κ => TrivOutside {s.v} κ ∧
      h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r))
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  exact ⟨s, τ, hs, hτ, GlobalTheory.RowLevelSplitData.fixed_ne_bot_of_fixed_vector_conj D.host.E D.R.r _ s τ h hτ f hfS hf0
    (fun κ h1 h2 => hfix κ ⟨h1, h2⟩)⟩

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in

theorem stepW_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

end GlobalTheory.RowDepthTrue

end

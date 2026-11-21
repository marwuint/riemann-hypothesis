import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlModel
variable {D : D7}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k),
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨gS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y' FS.β FS.γ FS.βγ FS.γβ
  obtain ⟨gT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q T Y FT.β FT.γ FT.βγ FT.γβ
  let α : GlobalTheory.FinPl.Frame q S Y' := ⟨FS.β, FS.γ, FS.βγ, FS.γβ, gS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T Y := ⟨FT.β, FT.γ, FT.βγ, FT.γβ, gT, hT1, hT2⟩
  obtain ⟨ΛS, i1, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y' α M hM
  obtain ⟨ΛT, i2, hβ, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q T Y β M' hM'
  refine ⟨⟨GlobalTheory.LatPair.latInd ΛS ΛT, GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT⟩, funext fun x => ?_⟩
  have hh := GlobalTheory.FinPl.HalfInd.isHalf_wr α β x
  have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hM hM' hU hα hβ hh
  have hr : GlobalTheory.FinPl.rd α β (GlobalTheory.FinPl.HalfInd.wr α β x) = x := by
    rw [GlobalTheory.FinPl.HalfInd.rd_eq]
    have : Matrix.map (GlobalTheory.FinPl.HalfInd.wr α β x) q.pr = FT.β * x * FS.γ := by
      ext i j; rw [Matrix.map_apply, GlobalTheory.FinPl.HalfInd.wr_apply, q.pr_sec]
    rw [this]
    change FT.γ * (FT.β * x * FS.γ) * FS.β = x
    rw [Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  rw [hr] at key
  change GlobalTheory.LatPair.latInd ΛS ΛT x = _
  unfold GlobalTheory.LatPair.latInd
  by_cases h : ∀ y ∈ ΛS, x *ᵥ y ∈ ΛT
  · rw [if_pos h, Set.indicator_of_mem (by exact key.2 h)]
  · rw [if_neg h, Set.indicator_of_notMem (by exact fun h' => h (key.1 h'))]

end Rel

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem e_mul_e (L L' : LocPl ψ S T M M') (h : L.q.v ≠ L'.q.v) : L.q.e * L'.q.e = 0 := by
  have h1 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L.q.v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L.q)
  have h2 : L.q.e * L'.q.e ∈ GlobalTheory.FinPl.idAt D (· = L'.q.v) := Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt L'.q)
  have h3 : GlobalTheory.FinPl.compAt D L.q.v (L.q.e * L'.q.e) = 0 := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h2).2 ⟨_, h⟩
  rw [GlobalTheory.FinPl.Model.eq_single h1, h3, map_zero]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SeeSaw.LocPlModel
end

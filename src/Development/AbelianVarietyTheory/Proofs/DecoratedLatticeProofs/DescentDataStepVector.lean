import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponents

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDat

theorem exists_o {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := GlobalTheory.SeeSaw.LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hTm a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hTm

theorem idem_eq {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.LocMod.PinInhab.idem_unique (hes _ (pl i).2) (ha i)

theorem isThetaAt_smul {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ} {f₀ Φ f : Mx D m n → ℂ}
    {κ : ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ B hs e Λ c f₀ (κ • Φ) f) : IsThetaAt ψ B hs e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨hex, hall⟩ := h
  refine ⟨hex, fun Tm hTm => ?_⟩
  rw [hall Tm hTm, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.MidDat


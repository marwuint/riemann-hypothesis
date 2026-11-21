import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowFamilyValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumFactorsOverTwistPrimesLocal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairProperty

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem comb_smul_coef {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (κ : ℂ) (d : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (κ • d) f = κ • comb ψ S T d f := by
  by_cases hκ : κ = 0
  · subst hκ; simp [comb]
  · unfold comb
    rw [Finsupp.support_smul_eq hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem isRatDatum_const_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D}
    {Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ} {f₀ f : WO S T → ℂ} (h : IsRatDatum ψ S T e Ξ f₀ f) (κ : ℂ) :
    IsRatDatum ψ S T e (fun z => κ * Ξ z) f₀ (κ • f) := by
  obtain ⟨Φ, hSB, hval, hth⟩ := h
  refine ⟨κ • Φ, ?_, fun γ => by simp [hval γ], ?_⟩
  · obtain ⟨hs, k, hk, hinv, hsupp⟩ := hSB
    refine ⟨fun t ht => hs t fun h0 => ht (by simp [h0]), k, hk, fun v hv hv' t => by simp [hinv v hv hv' t],
      fun t ht => hsupp t fun h0 => ht (by simp [h0])⟩
  · unfold IsThetaAt AllSome at hth ⊢
    refine ⟨hth.1, fun T hT => ?_⟩
    have h := hth.2 T hT
    simp only at h ⊢
    rw [h, map_smul]

def chartRescale {Ch : ℕ → Type} (m : ℕ) (cc : ℕ → ℂ) (b : ∀ j, Ch (j + 1) → ℂ) : ∀ j, Ch j → ℂ
  | 0 => fun _ => 1
  | j + 1 => fun γ => if j < m then cc j * b j γ else 1

theorem datRoot_ne_zero {x : ℂ} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) : x ≠ 0 := by
  obtain ⟨n, hn, hx⟩ := h
  rintro rfl
  simp [zero_pow hn.ne'] at hx

theorem datRoot_mul {x y : ℂ} (hx : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) (hy : ∃ n : ℕ, 0 < n ∧ y ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (x * y) ^ n = 1 := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, one_mul]

theorem datRoot_prod {ι : Type*} (s : Finset ι) (x : ι → ℂ) (h : ∀ i ∈ s, ∃ n : ℕ, 0 < n ∧ x i ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ (∏ i ∈ s, x i) ^ n = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact datRoot_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.Fam

end

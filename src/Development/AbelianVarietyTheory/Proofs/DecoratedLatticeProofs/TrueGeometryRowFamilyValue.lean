import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateDatumUnchangedFramesCongruentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem psiAt_one_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ S₁ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S₁) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu))
    (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu)
    (P' : Formalism.L2.Col.rowSG Pr sel mu') (hPP : P.1 = P'.1) (hmem : P.1 ∈ Pr.vGs) (hsh : cst.sharp = cst'.sharp)
    (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))) :
    Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y = Formalism.L2.Col.PsiAt Ch sel mu' cst' s P' 1 x y := by
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold Formalism.L2.Col.PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one]
  unfold Formalism.L2.Col.PhiAt
  rw [if_pos hmem, if_pos hmem', hsh, hPP]

theorem lastStepPoints_sub_integral_of_uniformiser_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S S' : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (h : valuation k (((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k)) ≤ 1) (r : GlobalTheory.StepData.XIx (Fin κ) t (s + 1)) :
    S.y0 t r - S'.y0 t r ∈ 𝒪[k] := by
  unfold GlobalTheory.SymChain.SymData.y0
  by_cases hr : r = Sum.inl (Sum.inr 0)
  · subst hr
    simp only [Pi.single_eq_same]
    have h3 := neg_mem (show ((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] from h)
    rwa [neg_sub] at h3
  · simp [Pi.single_eq_of_ne hr]

end GlobalTheory.Fam.PenLoc
end

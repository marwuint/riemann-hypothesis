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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.Fam.LevelFrames

open _root_.Formalism.L2.Col in

theorem redV_eq_of_near {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : y ∈ stdAt E n P) : redV P (f y) = redV P y := by
  funext i
  have hy' := GlobalTheory.TopStep.mem_stdAt.1 hy
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h : P.valuation E (f y i - y i) < 1 := by
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((GlobalTheory.AtTypeExists.intAt_iff _ _).1 (hy' j))) (hf i j)
  obtain ⟨h1, h2⟩ := twRed0_of_val P h
  have h3 := reduction_add h1 (hy' i)
  rw [sub_add_cancel, h2, zero_add] at h3
  exact h3

end GlobalTheory.Fam.LevelFrames

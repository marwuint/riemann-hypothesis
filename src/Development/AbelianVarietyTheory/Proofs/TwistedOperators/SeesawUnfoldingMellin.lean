import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFun

theorem conjugateUnitaryAdelicIso_map_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem algebraicDatum_eq_sum_pureTensors_vacua {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

end GlobalTheory.SquareAgree.LineDerFun

end

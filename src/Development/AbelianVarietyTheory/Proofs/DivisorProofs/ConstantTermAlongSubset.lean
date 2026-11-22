import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabili

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.ConstTrans
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem unip_eq_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := fun F E _ _ _ _ _ σ h n J hJ r X Y hW S m hm hm' => le_antisymm (_root_.GlobalTheory.StdPar.unip_le_unipFlag_initCols F E σ h n J hJ r X Y hW S m hm hm') (GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent F E σ h n J hJ r X Y hW S m hm hm')
theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := _root_.GlobalTheory.StdParFlag.unip_le_parFlag

end GlobalTheory.ConstTrans

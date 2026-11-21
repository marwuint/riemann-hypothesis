import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section
namespace GlobalTheory.RingIface
open Formalism Reformulated.AutPerF
open scoped Formalism.Per

namespace X
variable {l : ℕ} [Fact l.Prime]
theorem alg_mem_kerP {a : Per.Ainf l} (h : Per.θ l a = 0) : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l :=
  AlgebraMemThetaKernel.Bridge.alg_mem_kerP l h

theorem dp (x : Per.Ainf l) (n : ℕ) (y : Per.AinfP l) (hx : Per.θ l x = 0)
    (h : ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) : y ∈ Per.Acris0 l :=
  DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 l x n y hx h

theorem le (S : Subalgebra (Per.Ainf l) (Per.AinfP l)) (h : ∀ x : Per.Ainf l, Per.θ l x = 0 → ∀ (n : ℕ) (y : Per.AinfP l),
    y ∈ Per.Acris0 l → ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n → y ∈ S) :
    Per.Acris0 l ≤ S :=
  CrisZeroLeThird.Bridge.acris0_le_3 l S h

end X

variable (l : ℕ) [Fact l.Prime]

theorem phiA_teich (y : Per.Fl l) : Per.φA l (WittVector.teichmuller l y) = WittVector.teichmuller l (y ^ l) :=
  FrobeniusTeichmuller.Bridge.phiA_teich l y

theorem sigA_teich (g : Per.Gq l) (y : Per.Fl l) :
    Per.σA g (WittVector.teichmuller l y) = WittVector.teichmuller l (Per.σF g y) :=
  TeichmullerAction.Bridge.sigA_teich l g y

theorem sigA_coeff (g : Per.Gq l) (w : Per.Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) :=
  SigmaCoeffA.Bridge.sigA_coeff l g w n

theorem sigO_coe (g : Per.Gq l) (y : Per.OC l) : ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) :=
  IntegralActionCoe.Bridge.sigO_coe l g y

theorem sigC_cont (g : Per.Gq l) : Continuous (Per.σC g) :=
  ContinuousGalois.Bridge.sigC_cont l g

theorem tower (x : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) x =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  ScalarTowerAlt.Bridge.tower l x

theorem sigD_alg (g : Per.Gq l) (b : Per.BdRp l) : Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) b) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g b) :=
  DeRhamSigmaAlgebra.Bridge.sigD_alg l g b

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  EvaluationAlgebra.Bridge.ev_alg l n a

theorem ev_ext (y y' : Per.BdRp l) (h : ∀ n, Per.ev l n y = Per.ev l n y') : y = y' :=
  EvaluationExt.Bridge.ev_ext l y y' h

theorem phiA_coeff (w : Per.Ainf l) (n : ℕ) : (Per.φA l w).coeff n = w.coeff n ^ l :=
  FrobeniusCoeffA.Bridge.phiA_coeff l w n

theorem fontaineTheta_algebraMap (a : Per.Ainf l) :
    Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = ((Per.θ l a : Per.OC l) : ℂ_[l]) :=
  ThetaAlgebraMap.Bridge.fontaineTheta_algebraMap l a

theorem alg_mem_kerP {a : Per.Ainf l} (h : Per.θ l a = 0) : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l :=
  AlgebraMemThetaKernel.Bridge.alg_mem_kerP l h

theorem ev_surj (n : ℕ) : Function.Surjective (Per.ev l n) :=
  EvaluationSurjective.Bridge.ev_surj l n

theorem thetaD_alg (a : Per.AinfP l) : Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a :=
  ThetaDeRhamAlgebra.Bridge.thetaD_alg l a

theorem thetaD_of_mem_FilP {y : Per.BdRp l} (h : y ∈ Per.FilP l 1) : Per.θD l y = 0 :=
  ThetaOfFiltration.Bridge.thetaD_of_mem_FilP l h

theorem sigDp_alg (g : Per.Gq l) (a : Per.AinfP l) : Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
    algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  DividedPowerAlgebraMap.Bridge.sigDp_alg l g a

theorem isUnit_of_generator {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) :=
  IsUnitOfGenerator.Bridge.isUnit_of_generator l h

theorem exists_bdRp_equiv : ∃ e : Per.BdRp l ≃+* AdicCompletion (Per.kerP l) (Per.AinfP l),
    (∀ a, e (algebraMap (Per.AinfP l) (Per.BdRp l) a) = algebraMap _ _ a) ∧
      ∀ n y, AdicCompletion.evalₐ (Per.kerP l) n (e y) = Per.ev l n y :=
  DeRhamPlusEquivExists.Bridge.exists_bdRp_equiv l

theorem bcris_ext {R : Type} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x, f (algebraMap (Per.Acris l) (Per.Bcris l) x) = g (algebraMap (Per.Acris l) (Per.Bcris l) x)) : f = g :=
  PeriodRingExt.Bridge.bcris_ext l h

theorem alg_mem_FilD_nat {n : ℕ} {z : Per.BdRp l} (h : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l (n : ℤ) :=
  DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat l h

theorem exists_of_mem_FilD_nat {n : ℕ} {x : Per.BdR l} (h : x ∈ Per.FilD l (n : ℤ)) :
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x :=
  FiltrationNatExists.Bridge.exists_of_mem_FilD_nat l h

theorem zB_eq_aB_zA : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = Formalism.Per.aB l (Formalism.Per.zA l z) :=
  fun l _ ↦ GeneratorRelation.Bridge.zB_eq_aB_zA l

theorem mem_filtration_iff_mem_kerTheta_pow : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (y : Formalism.Per.BdRp l), y ∈ Formalism.Per.FilP l n ↔ Formalism.Per.ev l n y = 0 :=
  fun l _ ↦ DividedPowerFiltrationIff.Bridge.mem_filtration_iff_mem_kerTheta_pow l

theorem toC_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.OC l), Formalism.Per.toC l (algebraMap (Formalism.Per.OC l) (Localization.Away ((l : ℕ) : Formalism.Per.OC l)) a) = (a : ℂ_[l]) :=
  fun l _ ↦ CrisToComplexAlgebra.Bridge.toC_alg l

theorem padicIntMap_eq_algebraMap_comp : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zP l z = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z) :=
  fun l _ ↦ GeneratorAlgebraRelation.Bridge.padicIntMap_eq_algebraMap_comp l

theorem dividedPower_mem_Acris0 : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l :=
  fun l _ ↦ DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 l

theorem Acris0_le_of_dividedPowers : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S :=
  fun l _ ↦ CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers l

theorem aB_algebraMap_padicInt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.Ainf l) z) = Formalism.Per.zB l z :=
  fun l _ z ↦ (GeneratorRelation.Bridge.zB_eq_aB_zA l z).symm

theorem zD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  fun l _ ↦ DeRhamGeneratorAlgebra.Bridge.zD_eq_alg l

theorem aB_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l), Formalism.Per.aB l a = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) :=
  fun l _ ↦ PeriodMapApply.Bridge.aB_apply l

theorem aB_zl : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.Ainf l) z) = Formalism.Per.zB l z :=
  fun l _ z ↦ (GeneratorRelation.Bridge.zB_eq_aB_zA l z).symm

theorem zD_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  fun l _ ↦ DeRhamGeneratorAlgebra.Bridge.zD_eq_alg l

theorem mem_Acris0_of_factorial_mul : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l), Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l :=
  fun l _ ↦ CrisZeroFactorialMul.Bridge.mem_Acris0_of_factorial_mul l

theorem aB_apply : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l), Formalism.Per.aB l a = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) :=
  fun l _ ↦ PeriodMapApply.Bridge.aB_apply l

theorem aB_alg : ∀ (l : ℕ) [Fact l.Prime] (w : Formalism.Per.Ainf l), Formalism.Per.aB l w = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) w) :=
  fun l _ ↦ PeriodMapApply.Bridge.aB_apply l

theorem aB_zA : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (Formalism.Per.zA l z) = Formalism.Per.zB l z :=
  fun l _ ↦ PeriodGeneratorImage.Bridge.aB_zA l

theorem pD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  fun l _ ↦ DividedPowerApply.Bridge.pD_apply l

theorem alg_mem_FilD_zero : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.BdRp l), algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y ∈ Formalism.Per.FilD l 0 :=
  fun l _ ↦ DeRhamFiltrationZero.Bridge.alg_mem_FilD_zero l

theorem zB_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z)) :=
  fun l _ ↦ CrisGeneratorAlgebra.Bridge.zB_alg l

theorem acris0_le : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S :=
  fun l _ ↦ CrisZeroLeAlt.Bridge.acris0_le l

theorem acris0_le_3 : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), y ∈ Formalism.Per.Acris0 l → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S :=
  fun l _ ↦ CrisZeroLeThird.Bridge.acris0_le_3 l

theorem dividedPower_mem : ∀ (l : ℕ) [Fact l.Prime] (m : Formalism.Per.Ainf l) (j : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l m = 0 → ((j.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) m ^ j → y ∈ Formalism.Per.Acris0 l :=
  fun l _ ↦ DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0 l

theorem ev_sigDp : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.Per.Gq l) (n : ℕ) (y : Formalism.Per.BdRp l) (a : Formalism.Per.AinfP l), Formalism.Per.ev l n y = Ideal.Quotient.mk _ a → Formalism.Per.ev l n (Formalism.Per.σDp g y) = Ideal.Quotient.mk _ (Formalism.Per.extP (Formalism.Per.σA g) a) :=
  fun l _ ↦ EvaluationDividedPower.Bridge.ev_sigDp l

end GlobalTheory.RingIface

import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.FactorialMulTruncLog
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open scoped Formalism.Per

namespace GlobalTheory.AdicMaps

open Formalism

noncomputable section

section Gen
variable {R S : Type} [CommRing R] [CommRing S]

def levMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ) :
    R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Reformulated.AutPerF.pow_le_comap_pow hf n)

def adicMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  Reformulated.AutPerF.adicMap I J f hf

theorem adicMap_alg (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (r : R) :
    adicMap I J f hf (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by
  first | exact @AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg | exact AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg .. | (intros; apply AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg <;> assumption)

abbrev PHat (p : ℕ) (R : Type) [CommRing R] : Type := AdicCompletion (Ideal.span {(p : R)}) R

def padicMap (p : ℕ) (f : R →+* S) : PHat p R →+* PHat p S :=
  Reformulated.AutPerF.adicMap _ _ f (Reformulated.AutPerF.span_natCast_le_comap p f)

theorem padicMap_alg (p : ℕ) (f : R →+* S) (r : R) :
    padicMap p f (algebraMap R (PHat p R) r) = algebraMap S (PHat p S) (f r) := by
  first | exact @PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg | exact PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg .. | (intros; apply PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg <;> assumption)

end Gen

theorem exists_acris_completion (l : ℕ) [Fact l.Prime] :
    ∃ e : Per.Acris l ≃+* AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l),
      ∀ s : Per.Acris0 l, e (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l)) s := by
  first | exact @CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion | exact CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion .. | (intros; apply CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion <;> assumption)

theorem coeff_galois (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : Per.Fl l)
    (n : ℕ) (y : Per.OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    PreTilt.coeff n (Per.σF g x) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (Per.σO g y) := by
  first | exact @AdicCoeffGalois.Bridge.AdicMaps.coeff_galois | exact AdicCoeffGalois.Bridge.AdicMaps.coeff_galois .. | (intros; apply AdicCoeffGalois.Bridge.AdicMaps.coeff_galois <;> assumption)

end

end GlobalTheory.AdicMaps

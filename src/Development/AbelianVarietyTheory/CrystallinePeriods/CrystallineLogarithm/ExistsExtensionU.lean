import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.PadicField
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
namespace CrisHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bcris_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
  refine RingHom.congr_fun (Reformulated.AutPerF.BcrisPlus.hom_ext
    (f := f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _))
    (g := g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l ↥(PadicComplexInt l)) _)) fun x => ?_) y
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h x

end
end CrisHomExtUnit
namespace CrisExtensionUnit
namespace Bridge.CrisLoc.CrisExtensionUnitLemmas

end Bridge.CrisLoc.CrisExtensionUnitLemmas

end CrisExtensionUnit
namespace DeRhamHomExtUnit
section
universe u

theorem Bridge.CrisLoc.bdR_hom_ext_u : ∀ (l : ℕ) [Fact l.Prime] {R : Type u} [CommRing R] {f g : (Reformulated.AutPerF.BdR l ↥(PadicComplexInt l)) →+* R} (h : ∀ x : (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l)), f (algebraMap _ _ x) = g (algebraMap _ _ x)), f = g := by
  intro l _ R _ f g h
  exact IsLocalization.ringHom_ext
    (nonZeroDivisors (Reformulated.AutPerF.BdRPlus l ↥(PadicComplexInt l))) (RingHom.ext h)

end
end DeRhamHomExtUnit

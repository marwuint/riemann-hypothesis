import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology

noncomputable section

namespace GlobalTheory.ThetaCplV

open scoped ComplexConjugate
section Abstract

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {Gr : Type*} [Group Gr]

def rt {G : Type*} [Group G] (K : Subgroup G) : K →* Module.End ℂ (G → ℂ) where
  toFun k := LinearMap.funLeft ℂ ℂ fun x => x * (k : G)
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' k k' := by ext f x; simp [LinearMap.funLeft_apply, mul_assoc]

@[simp] theorem rt_apply {G : Type*} [Group G] (K : Subgroup G) (k : K) (f : G → ℂ) (x : G) :
    rt K k f x = f (x * k) := rfl

end Abstract

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThetaCplV

end

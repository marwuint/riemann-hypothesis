import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt.Inhab

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsGalois ℚ QI := IsCyclotomicExtension.isGalois {4} ℚ QI

def threeZ : Ideal ℤ := Ideal.span {((3 : ℕ) : ℤ)}

instance : threeZ.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2 (Nat.prime_iff_prime_int.mp Nat.prime_three)

end GlobalTheory.FunExt.Inhab

end

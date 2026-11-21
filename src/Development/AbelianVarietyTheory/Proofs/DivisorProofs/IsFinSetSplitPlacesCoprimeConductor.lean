import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.InhabK

section Cyclotomic

abbrev K : Type := CyclotomicField 21 ℚ

instance : IsCyclotomicExtension {21} ℚ K := CyclotomicField.isCyclotomicExtension 21 ℚ

instance : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {21}) ⟨21, rfl, by norm_num⟩

end Cyclotomic

end GlobalTheory.CMVal.InhabK

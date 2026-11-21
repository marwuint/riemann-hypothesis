import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.LemmaX
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Shapiro
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.CardCohomologyZeroMackeyRepOfNeTop
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ApplySubrepresentationCongr
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ToFunEqZeroOfForallIsCyclic
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable def resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield) [Fact (K ≤ K')]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) :
    Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) :=
  Rep.res (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom
    (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)

instance isDiscreteRep_resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield)
    [Fact (K ≤ K')] (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] :
    IsDiscreteRep (resTo S K' hK' M) :=
  isDiscreteRep_res_gsBaseChange_symm S hK' _

end PositivityTheory.Lit1.GEN.W_killed_a

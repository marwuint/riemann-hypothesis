import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesMetRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.EndModel
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem endData_of_oAct {R : Type} [CommRing R] [IsDomain R] (O : Type) [Ring O] [StarRing O] (D : DegPre R)
    [Module O D.X] (io : D.OAct O) (a : O) :
    EndData D (io.onB.act a) (io.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨io.onB.hom a, io.onB.hom (star a), io.onB.rosati a, io.c_lin a, io.c_lin (star a), io.tau_bal a⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem thickMap_map {G H : Over (Sp R)} (b : G ⟶ H) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e H := by
  apply pullback.hom_ext
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
    rfl
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    simp
    erw [pullback.lift_snd_assoc]

end GlobalTheory.Mum.EndModel

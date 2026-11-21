import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LevPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Classes

open GlobalTheory.Mass Formalism.IndefR.Lev Formalism.L2.DIV

def finP (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (GlobalTheory.LevSplit.finE_mem_UA V)

theorem coe_finP (V : HSp D) (h : GA D V) : (finP V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

end Classes

section Local

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem mem_hatL_iff [Module.Finite (𝓞 E) Λ] (z : Fin n → E ⊗[F] 𝔸) :
    z ∈ hatL (F := F) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (z i)) ∈ locL v Λ :=
  mem_latS_adele_iff Λ z

end Local

section Level

open Formalism.L2.Geo.Def Formalism.IndefR.Lev Formalism.L2.DIV
open Formalism.UG (levelVL levelAfL prV bc stabGL)

variable (D)

variable {D}

instance finite_latC (V : HSp D) : Module.Finite (𝓞 D.host.E) (latC V) :=
  Module.Finite.iff_fg.2 (latHat_eq_hat_and_gram D V).2.2.1

end Level

end GlobalTheory.LevPin

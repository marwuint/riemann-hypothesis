import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Et

structure SlopeTestRemainingChoices : Prop where
  sheaf : type_of% @_root_.GlobalTheory.EtC.sec_ext_glue
  resol : type_of% @GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
  freeS : type_of% @GlobalTheory.T.free_sections_ext_res_map
  evs : type_of% @GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties
  rep : type_of% @_root_.GlobalTheory.EtC.sch_cls_cocycle_sec
  sec : type_of% @GlobalTheory.T.degreeZeroSectionClass_properties
  aw : type_of% @GlobalTheory.T.cup_eq_class_of_isAW
  twist : type_of% @GlobalTheory.T.tateTwist_sections_locally_generated
  pair : type_of% @GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique
  unit : type_of% @GlobalTheory.T.tateTwistUnitClass_rootClass_spec

section Site
variable {C : Type 1} [Category.{0} C] {S : Type 1} [CommRing S]

abbrev PM (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] : Type 2 := Cᵒᵖ ⥤ ModuleCat.{1} S

abbrev pmAp {F G : PM C S} (φ : F ⟶ G) {U : C} (x : F.obj (op U)) : G.obj (op U) := (φ.app (op U)).hom x

structure Dat (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] (ι : Type) where
  P : ι → ℤ → PM C S
  dP : ∀ b s t, P b s ⟶ P b t
  Q : ℤ → PM C S
  dQ : ∀ s t, Q s ⟶ Q t
  e : ι → ℤ
  φ : ∀ b s, P b (s - e b) ⟶ Q s
  ddP : ∀ b s t u, dP b s t ≫ dP b t u = 0
  ddQ : ∀ s t u, dQ s t ≫ dQ t u = 0
  comm : ∀ b s t, s + 1 = t → φ b s ≫ dQ s t = dP b (s - e b) (t - e b) ≫ φ b t

variable {ι : Type} [Fintype ι] (D : Dat C S ι)

def Dat.sm {U : C} (s : ℤ) (a : ∀ b, (D.P b (s - D.e b)).obj (op U)) : (D.Q s).obj (op U) := ∑ b, pmAp (D.φ b s) (a b)

def Dat.Ker {V : C} (s : ℤ) (a : ∀ b, (D.P b (s - D.e b)).obj (op V)) : Prop :=
  (∀ b, pmAp (D.dP b (s - D.e b) (s + 1 - D.e b)) (a b) = 0) ∧ ∃ y' : (D.Q (s - 1)).obj (op V), D.sm s a = pmAp (D.dQ (s - 1) s) y'

end Site

section Rep
variable {R : Type} [CommRing R]

variable {S Y : Scheme.{0}} (p' : Y ⟶ S)

def bm {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) : pullback v p' ⟶ pullback u p' :=
  ((Over.pullback p').map (Over.homMk g h : Over.mk v ⟶ Over.mk u)).left

@[reassoc (attr := simp)]
theorem bm_fst {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) :
    bm p' g h ≫ pullback.fst u p' = pullback.fst v p' ≫ g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bm_snd {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) :
    bm p' g h ≫ pullback.snd u p' = pullback.snd v p' := pullback.lift_snd _ _ _

end Rep

end UpperTheory.Et

end

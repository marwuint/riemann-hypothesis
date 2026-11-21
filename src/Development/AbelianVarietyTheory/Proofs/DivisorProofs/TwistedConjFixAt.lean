import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

end GlobalTheory.BigOn.Exp.TwConj

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem unr_algNorm {a : ℕ} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (algNorm σ)).unr := by
  rw [rec_algNorm hrc, WD.unr_tw]
  exact unr_rec_of_hasSat hrc σ S hS

variable [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

end UpperTheory.GalN.V

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VAddNonnegOfInt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (I.rec7 l Z) := by
  intro B X I hI hP l Z hR
  obtain ⟨C, hC, _⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hI hP l Z
  exact _root_.GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 _ (Formalism.MainNotions.RT.PeriodPointConditions.perDec0_of_cols C
    (fun u => GlobalTheory.PerDecAtRef.perDec0At_std I hI l Z hR u _ _ (C.forms u) (hC u)))

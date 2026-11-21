import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOffStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.twLev_prime : GlobalTheory.AdForm.TwLev' := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ hJall j hj b
  refine ⟨fun i g hg => ⟨_root_.GlobalTheory.AdForm.StabLev.stab_mem_level I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg,
    _root_.GlobalTheory.AdForm.chi_std_trivial I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg _⟩, fun κ hκ => ?_⟩
  obtain ⟨g, hg1, κ', hκ', heq⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off (I.rec7 l Z) ((I.rec7 l Z).sp.X j) k ι p _ (β j)
    (_root_.GlobalTheory.AdForm.StdT.places_injective I hOk hPins l Z u p β Q L hS) J hJ hJall κ
  exact ⟨g, fun i => _root_.GlobalTheory.AdForm.comp_fixes_stdPair I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b κ hκ i (g i) (hg1 i), κ', hκ', heq⟩

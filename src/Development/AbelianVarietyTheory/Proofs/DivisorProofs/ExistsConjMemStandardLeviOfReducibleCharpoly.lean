import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitFactorRegularSemisimpleReducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIdempotentOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIdempotentGivesDualStableSubspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasesIsotropicSubspacesDuality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCarryHyperbolicFamilyWittFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemStandardLeviWittFrame

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.ConjLevi

theorem exists_conj_mem_levi : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  intro D V hr hRS Φ γ hss hirr hnf
  have hreg := _root_.GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -, hR, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨k, K, hK1, hK2, he, i, hi⟩ := _root_.GlobalTheory.SplitFactor.exists_split_factor D.sp.cm.sig V.gram γ.1 hr hss hA hR hirr hnf
  obtain ⟨ε, hεL, hεε, hε0, hεi⟩ :=
    @_root_.GlobalTheory.SplitFactorIdem.exists_isotropic_idempotent _ _ _ _ _ _ _ D.sp.cm.sig V.gram γ.1 hreg hA hP k K hK1 hK2 he i hi
  obtain ⟨X, X', hX0, hXi, hX'i, hXs, hX's, hn1, hn2⟩ := _root_.GlobalTheory.IdemIsotropic.idem_isotropic_pair γ ε hεL hεε hε0 hεi
  obtain ⟨a, x, x', ha0, ha, hx, hx', hli, hee, hff, hef⟩ := _root_.GlobalTheory.IsoDuality.exists_dual_bases X X' hX0 hXi hX'i hn1 hn2
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.WittCarry.exists_GF_carry_hyperbolic Φ ha x x' hli hee hff hef
  refine ⟨g, {stdVec ⟨a - 1, by omega⟩}, ?_, Finset.singleton_nonempty _, ?_⟩
  · have := isPar_stdPar ({⟨a - 1, by omega⟩} : Finset (Fin (wittIndex V)))
    simpa [stdPar] using this
  · exact _root_.GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec Φ γ g ha ⟨a - 1, by omega⟩ (by simp only; omega) x x' (fun i => (hg i).1)
      (fun i => (hg i).2) (by rw [hx]; exact hXs) (by rw [hx']; exact hX's)

end GlobalTheory.ConjLevi

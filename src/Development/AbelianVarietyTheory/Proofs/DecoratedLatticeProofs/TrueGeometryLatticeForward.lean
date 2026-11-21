import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegralStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LatFwd

theorem finM_inv_eq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    have e2 : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [e1, e1, ← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem proj_mem_stabLoc_std {D : D7} (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g⁻¹)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.stdLattice D.host.E V.rank) v := by
  rw [map_inv, map_inv] at hM'
  set M := GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  have hint : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

end GlobalTheory.FamTrace.LatFwd

namespace GlobalTheory.FamTrace.LatFwd

end GlobalTheory.FamTrace.LatFwd

end

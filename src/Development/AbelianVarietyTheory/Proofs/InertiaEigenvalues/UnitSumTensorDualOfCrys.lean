import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart

noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (LocQuotCrys LocTensorCrys LocDualCrys)

set_option synthInstance.maxHeartbeats 400000

variable {l : ℕ} [Fact l.Prime]

private theorem frobW_surjective_lemma : Function.Surjective (frobW l) := by
  have hC : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have hf : Function.Surjective (frobenius (Cb l) l) := by
    first
      | exact surjective_frobenius (Cb l) l
      | exact (bijective_frobenius (Cb l) l).2
      | exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩
  intro y
  obtain ⟨x, hx⟩ := WittVector.map_surjective (p := l) _ hf y
  unfold frobW
  exact ⟨x, hx⟩

theorem φRW_surjective (LL : FinExt l) : Function.Surjective (φRW LL) := by
  have hg : Function.Surjective (frobW l).toLinearMap := frobW_surjective_lemma
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (↥(OL LL)) hg y
  refine ⟨x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φRW]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem map_ne_top {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (m : Ideal W.EE) (hm : m.IsMaximal) :
    m.map E.tie.ioE.toRingHom ≠ ⊤ := by
  have : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.EtaleExact.finite_OL LL
  have : IsNoetherianRing ↥(OL LL) := by
    first
      | infer_instance
      | exact isNoetherian_of_tower ℤ_[l] inferInstance
  refine GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm
  · rw [P.PD_p K]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c
  · exact GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)

theorem descends {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) : Descends E.tie := by
  intro ι _ M w hg hw i
  exact _root_.GlobalTheory.FrobDescent.mem_range_of_fixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i

end GlobalTheory.WachTensor

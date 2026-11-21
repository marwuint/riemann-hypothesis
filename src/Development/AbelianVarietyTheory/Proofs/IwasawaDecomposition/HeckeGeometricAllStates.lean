import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeoOfLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

end GlobalTheory.HeightCounting.HeckeLaw

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy


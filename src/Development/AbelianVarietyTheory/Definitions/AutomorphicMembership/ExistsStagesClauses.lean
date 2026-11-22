import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsMuIsRamified
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotMtStableOfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsParametersOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

theorem conj_mem {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) {w : X.B.places.Pl} (hw : w ∈ Wt) : X.B.places.conj w ∈ Wt := by
  rw [mem_iff h, X.W.muAt_conj]
  exact (mem_iff h w).1 hw

theorem Q_off {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) {w : X.B.places.Pl} (hw : w ∉ Wt) : T.Q w = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v => ((T.psi_is w).ram v).1 (h.supp w hw ▸ isClsF_one.unr v)

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)

def glue {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]
    (A : HeightOneSpectrum (𝓞 L) → Submodule (𝓞 L) V) : Submodule (𝓞 L) V where
  carrier := {x | ∀ w, ∃ d : 𝓞 L, d ∉ w.asIdeal ∧ d • x ∈ A w}
  add_mem' := fun {x y} hx hy w => by
    obtain ⟨d, h1, h2⟩ := hx w
    obtain ⟨e, h3, h4⟩ := hy w
    refine ⟨d * e, fun h => (w.isPrime.mem_or_mem h).elim h1 h3, ?_⟩
    rw [smul_add]
    exact add_mem (by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h2) (by rw [mul_smul]; exact Submodule.smul_mem _ _ h4)
  zero_mem' := fun w => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := fun a x hx w => by
    obtain ⟨d, h1, h2⟩ := hx w
    exact ⟨d, h1, by rw [smul_comm]; exact Submodule.smul_mem _ _ h2⟩

end GlobalTheory.Mem.Top.V4.Model

end

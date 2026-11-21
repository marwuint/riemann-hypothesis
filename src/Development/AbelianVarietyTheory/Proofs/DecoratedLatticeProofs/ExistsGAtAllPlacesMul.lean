import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

end SlopeTestRemainingChoices

end GlobalTheory.LocMod.PinInhab
end

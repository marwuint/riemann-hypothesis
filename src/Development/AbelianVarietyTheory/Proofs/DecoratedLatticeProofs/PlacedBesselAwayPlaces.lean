import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemGluedIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

noncomputable section

namespace GlobalTheory.MiTop.LineAtT

variable {D : D7}

def UnitScal (v : GlobalTheory.FinPl.Pl D) (t : D.host.E) : Prop :=
  ∀ a ∈ idAt D (· = v), incA D t * a ∈ intAt D (· = v) ↔ a ∈ intAt D (· = v)

theorem UnitScal.mul {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hs : UnitScal v s) (ht : UnitScal v t) : UnitScal v (s * t) := fun a ha => by
  rw [RingHom.map_mul, mul_assoc, hs _ (Ideal.mul_mem_left _ _ ha), ht a ha]

theorem UnitScal.cancel {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hst : UnitScal v (s * t)) (ht : UnitScal v t) : UnitScal v s := fun a ha => by
  rw [← hst a ha, ← ht _ (Ideal.mul_mem_left _ _ ha), RingHom.map_mul, ← mul_assoc, mul_comm (incA D t)]

theorem unitAt_one (v : GlobalTheory.FinPl.Pl D) : UnitScal v 1 := fun a _ => by rw [RingHom.map_one, one_mul]

theorem UnitScal.pow {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) (n : ℕ) : UnitScal v (s ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one v
  | succ n ih => rw [pow_succ]; exact ih.mul hs

theorem UnitScal.neg {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) : UnitScal v (-s) := fun a ha => by
  rw [← hs a ha, RingHom.map_neg, neg_mul]
  exact ⟨fun h => neg_neg (incA D s * a) ▸ GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩

theorem unitAt_of {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : s ≠ 0)
    (h : ∀ a ∈ intAt D (· = v), incA D s * a ∈ intAt D (· = v) ∧ incA D s⁻¹ * a ∈ intAt D (· = v)) : UnitScal v s := fun a _ => by
  refine ⟨fun h1 => ?_, fun h1 => (h a h1).1⟩
  have := (h _ h1).2
  rwa [← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hs, RingHom.map_one, one_mul] at this

theorem unitAt_nat {v : GlobalTheory.FinPl.Pl D} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) : UnitScal v (N : D.host.E) := by
  have hN : (N : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hv (by simp)
  refine unitAt_of hN fun a ha => ⟨GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha, GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha⟩
  · rw [← Nat.cast_mul]; exact isIntegral_natCast _
  · rw [mul_inv_cancel₀ hN]; exact isIntegral_one

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAt_val (p : SplitPt D k) {t : D.host.E} (h1 : valuation k (p.pr (incA D t)) = 1)
    (h2 : valuation k (p.pr (incA D (star t))) = 1) : UnitScal p.v t := fun a ha => by
  rw [GluedLine.mem_intAt_iff p (Ideal.mul_mem_left _ _ ha), GluedLine.mem_intAt_iff p ha, RingHom.map_mul, RingHom.map_mul (cA D),
    RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]
  simp only [Valuation.mem_integer_iff, map_mul, h1, h2, one_mul]

theorem psiE_triv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA) {s : AE D}
    (hs : s ∈ idAt D (· = p.v)) : (∀ o ∈ intAt D (· = p.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = p.v) := by
  rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ p.v s hs, ← (GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hU 1 s).1, pow_one]

theorem psiE_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA)
    (q : GlobalTheory.LatPair.Unif k) : ∃ s, psiE ψ s ≠ 1 := by
  by_contra hc
  push_neg at hc
  have h := (psiE_triv hψ p hU (GlobalTheory.FinPl.FrameLat.sec_mem_idAt p q.inv)).1 fun o _ => hc _
  have h1 := GluedLine.pr_mem_of_intAt p h.2
  rw [p.pr_sec] at h1
  have h2 : IsUnit (q.1 : 𝒪[k]) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero))
  exact q.mem_max h2

theorem ne_zero_of_line {L : TH.HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : ζ ≠ 0 := by
  rintro rfl
  exact h.2 (by simp)

theorem vecB_ne {S A L : TH.HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : vecB o ζ ≠ 0 := fun e => by
  apply h.2
  have e' : o.iB *ᵥ ζ = 0 := e
  rw [← o.isoB, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero, dotProduct_zero]

theorem wittDecomposition_inclusion_mulVec_rationalVector {S S₀ : TH.HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) :
    d.j0 *ᵥ ratV z = ratV (d.i₀ *ᵥ z) := funext fun r => (RingHom.map_mulVec (incA D) d.i₀ z r).symm

theorem first_scale (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    {ψ : AddChar (AF D.host.F) ℂ} (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (hne : ∃ s, psiE ψ s ≠ 1) (hr : 0 < D.R.rS) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E}
    (hμ : μ ≠ 0) (hz : ∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) r))) :
    ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ r, B.d.jX r ⟨0, hr⟩ =
      incA D (μ * lam ^ D.R.rS) * incA D (X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (rank_eq X h) r))) := by
  obtain ⟨lam, hl, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := hB μ B.vA hμ
  refine ⟨lam, hl, fun r => ?_⟩
  rw [FirstVec.first_eq (d' := B'.d) (z := vecB B.o B.ζ) (z' := vecB B'.o B'.ζ) hne (vecB_ne _ B.line) (vecB_ne _ B'.line)
    (by rw [wittDecomposition_inclusion_mulVec_rationalVector, wittDecomposition_inclusion_mulVec_rationalVector, funext hz, funext hz']) (Subgroup.ext fun n => (B.tieN n).trans (B'.tieN n).symm)
    (fun n hn => star_injective ((B.tieψ n hn).trans (B'.tieψ n ((B'.tieN n).2 ((B.tieN n).1 hn))).symm)) hr r,
    ← RingHom.map_mul]
  exact congrArg (incA D) (he r ⟨0, hr⟩)

end GlobalTheory.MiTop.LineAtT

end

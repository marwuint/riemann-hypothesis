import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

variable {a : XPart D u} {b : YPart a}

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end

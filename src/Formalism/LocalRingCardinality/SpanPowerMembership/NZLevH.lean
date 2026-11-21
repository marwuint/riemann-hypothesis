import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevG
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

theorem natAct_inv_self (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (x : P.Xsp) : P.natAct A⁻¹ (P.natAct A x) = x := by
  have := jd_natAct_mul P A⁻¹ A
  have h2 : (fun v => (A⁻¹) v * A v) = (fun _ => (1 : GL (Fin (P.m + 1)) _)) := by
    funext v; rw [Pi.inv_apply, inv_mul_cancel]
  rw [h2, jd_natAct_one] at this
  exact (LinearMap.congr_fun this x).symm

include hp in

def Γsub : Subgroup ((∀ v, GL (Fin (P.m + 1)) (P.Qq v)) × Oˣ) where
  carrier := {γ | ∃ z : ℤ, P.natAct γ.1 (EV P) = ((p : Kf) ^ z * algebraMap O Kf ((γ.2⁻¹ : Oˣ) : O)) • EV P}
  mul_mem' := by
    rintro ⟨A, u⟩ ⟨B, w⟩ ⟨z, hz⟩ ⟨z', hz'⟩
    refine ⟨z + z', ?_⟩
    show P.natAct (fun v => A v * B v) (EV P) = _
    rw [jd_natAct_mul, LinearMap.comp_apply]
    simp only at hz hz'
    rw [hz', LinearMap.map_smul, hz, smul_smul]
    congr 1
    simp only [Prod.snd_mul, mul_inv_rev, Units.val_mul, map_mul, zpow_add₀ hp]
    ring
  one_mem' := ⟨0, by
    show P.natAct (fun _ => 1) (EV P) = _
    rw [jd_natAct_one]; simp⟩
  inv_mem' := by
    rintro ⟨A, u⟩ ⟨z, hz⟩
    simp only at hz
    refine ⟨-z, ?_⟩
    have hu : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hc : (p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O) ≠ 0 := by
      refine mul_ne_zero (zpow_ne_zero _ hp) fun h => ?_
      rw [h, zero_mul] at hu; exact zero_ne_one hu
    show P.natAct A⁻¹ (EV P) = _
    have h1 : EV P = P.natAct A (((p : Kf) ^ z * algebraMap O Kf ((u⁻¹ : Oˣ) : O))⁻¹ • EV P) := by
      rw [LinearMap.map_smul, hz, smul_smul, inv_mul_cancel₀ hc, one_smul]
    conv_lhs => rw [h1, natAct_inv_self]
    congr 1
    simp only [Prod.snd_inv, inv_inv, zpow_neg]
    rw [mul_inv, inv_eq_of_mul_eq_one_right hu]

include hp in

def levB : Level P where
  Γ := Γsub P hp
  act v := (Pi.evalMonoidHom (fun v => GL (Fin (P.m + 1)) (P.Qq v)) v).comp ((MonoidHom.fst _ _).comp (Γsub P hp).subtype)
  χ := (MonoidHom.snd _ _).comp (Γsub P hp).subtype

theorem levB_actX (γ : ↥(Γsub P hp)) : (levB P hp).actX γ = P.natAct γ.1.1 := rfl

theorem levB_chi (γ : ↥(Γsub P hp)) : ((levB P hp).χ γ : O) = (γ.1.2 : O) := rfl

end Formalism.BasicNotions.Examples₂.NZ

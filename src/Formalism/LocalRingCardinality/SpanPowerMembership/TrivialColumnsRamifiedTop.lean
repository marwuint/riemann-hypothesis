import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

abbrev FU : Type := Unit → Unit → ℂ

def cst : ℂ ≃ₗ[ℂ] FU where
  toFun z := fun _ _ => z
  invFun f := f () ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ip1 : (Unit → ℂ) →ₗ⋆[ℂ] (Unit → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => starRingEnd ℂ (f ()) * g ())
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc]) (by intros; simp [mul_add])
    (by intros; simp; ring)

section Chi

variable (T : ℕ) [hT : Fact T.Prime]

def chiU : (ZMod T)ˣ →* ℂˣ :=
  ((quadraticChar (ZMod T)).ringHomComp (Int.castRingHom ℂ)).toUnitHom

theorem chiU_val (a : (ZMod T)ˣ) :
    ((chiU T a : ℂˣ) : ℂ) = ((quadraticChar (ZMod T) (a : ZMod T) : ℤ) : ℂ) := by
  unfold chiU
  rw [MulChar.coe_toUnitHom]
  rfl

theorem chiU_pm (a : (ZMod T)ˣ) : ((chiU T a : ℂˣ) : ℂ) = 1 ∨ ((chiU T a : ℂˣ) : ℂ) = -1 := by
  rw [chiU_val]
  rcases quadraticChar_dichotomy a.ne_zero with h | h <;> rw [h] <;> simp

theorem chiU_sum (hT2 : T ≠ 2) [Fintype (ZMod T)ˣ] : ∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) = 0 := by
  obtain ⟨b, hb⟩ := quadraticChar_exists_neg_one (F := ZMod T) (by rw [ZMod.ringChar_zmod_n]; exact hT2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : ((chiU T (Units.mk0 b hb0) : ℂˣ) : ℂ) = -1 := by
    rw [chiU_val, Units.val_mk0, hb]; simp
  have h2 : ∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) =
      ∑ a : (ZMod T)ˣ, ((chiU T (Units.mk0 b hb0 * a) : ℂˣ) : ℂ) :=
    (Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 b hb0)) _ _ (fun _ => rfl)).symm
  have h3 : ∑ a : (ZMod T)ˣ, ((chiU T (Units.mk0 b hb0 * a) : ℂˣ) : ℂ) =
      -∑ a : (ZMod T)ˣ, ((chiU T a : ℂˣ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, Units.val_mul, h1]; ring
  rw [h3] at h2
  exact self_eq_neg.mp h2

def rho1 : (ZMod T)ˣ →* (FU →ₗ[ℂ] FU) :=
  (algebraMap ℂ (Module.End ℂ FU)).toMonoidHom.comp ((Units.coeHom ℂ).comp (chiU T))

theorem first_order_lift_apply (a : (ZMod T)ˣ) (φ : FU) : rho1 T a φ = ((chiU T a : ℂˣ) : ℂ) • φ := rfl

end Chi

variable (Tau : Type) [Fintype Tau]

abbrev chain1 : ColumnChain R0 Tau (fun _ => hc0) :=
  { emptyColumnChain Tau with
    cls := fun _ => Unit
    clsFin := fun _ => inferInstance
    stab := fun _ _ => Unit
    stabGrp := fun _ _ => inferInstance
    stabFin := fun _ _ => inferInstance
    dvd_DGam := fun _ _ _ => by simp
    rhoDet := fun _ _ => 1
    rhoDet' := fun _ _ => 1
    rho_norm := fun _ _ _ => by simp
    rho'_norm := fun _ _ _ => by simp
    unf := fun _ _ _ => LinearMap.id }

variable (T : ℕ) [hT : Fact T.Prime]

abbrev baseColumnsAt (Dst : ℝ) (hD : 0 < Dst) : ColumnsAtT R0 (chain1 Tau) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin 8
    card_vT := by simp [exampleRanks_f]
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => rho1 T
    Mu0 := ⊤
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => le_top
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := 2
    one_lt_gammaP := one_lt_two }

end Formalism.BasicNotions.Examples₂.ND

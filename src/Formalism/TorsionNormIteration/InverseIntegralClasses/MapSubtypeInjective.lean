import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.LogDeterminesLaw

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.Asm

open Formalism.G

section Integral

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_add {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a + b) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) (hb d))

theorem integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem integralMv_X {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem funEqMv_add {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a + b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_add ha hb using 1
  simp only [map_add, smul_add]
  abel

theorem funEqMv_sub {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a - b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_sub ha hb using 1
  simp only [map_sub, smul_sub]
  abel

end Integral

theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero

theorem two_le_q {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  obtain ⟨hp, ⟨k, hk, rfl⟩, -⟩ := h
  exact hp.two_le.trans (Nat.le_self_pow (by omega) _)

theorem funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ (f.subst h)) : IntegralMv h :=
  h2 K ι (IsFunEqTypeMv p q (q_ne_zero hS) σ) f hf0 hf1
    (fun _ _ ha hb => funEqMv_sub _ _ ha hb)
    (fun P hP0 hPI => hk K p q (q_ne_zero hS) σ hS f hf0 hfE ι P hP0 hPI)
    (fun D hD N hN hlow d hd => h3 K ι p q (q_ne_zero hS) σ (two_le_q hS) D hD N hN hlow d hd)
    h hh0 hC

theorem FunEqGroup_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  have hq := q_ne_zero hS
  have hG0 : MvPowerSeries.constantCoeff (atX f + atY f) = 0 := by
    rw [map_add, atX, atY, PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0, add_zero]
  have hGE : IsFunEqTypeMv p q hq σ (atX f + atY f) :=
    funEqMv_add hq σ (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 0))
      (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 1))
  obtain ⟨F, hF0, hF⟩ := h1 K (Fin 2) f (atX f + atY f) hf0 hf1 hG0
  refine ⟨F, hF0, funEqInv h2 h3 hk hS hf0 hf1 hfE F hF0 ?_, hF⟩
  rw [hF]
  exact hGE

theorem funEqType_unit {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg (d ())
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rw [hd]
  exact this

theorem FunEqHom_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI : IntegralMv h := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 (by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE)
  exact ⟨h, hh0, fun n => hI _, hh⟩

section FG

open Formalism.G.LogP

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries τ (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d F, hF d⟩

theorem coeff_lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) (d : τ →₀ ℕ) :
    ((MvPowerSeries.coeff d (lift F hF) : unitBall K) : K) = MvPowerSeries.coeff d F := rfl

end FG

end Formalism.LT.Asm

namespace Formalism.LT

theorem FunEqGroup_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} :=
  Formalism.LT.Asm.FunEqGroup_of' h1 h2 h3 hk

theorem FunEqHom_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk

end Formalism.LT

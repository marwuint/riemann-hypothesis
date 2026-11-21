import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
noncomputable section
namespace GlobalTheory.PhiGam.Model
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section
variable (k : Type) [Field k]

theorem algebraMap_eq (c : k) : algebraMap k k⸨X⸩ c = HahnSeries.C c := by rw [HahnSeries.algebraMap_apply', ← HahnSeries.ofPowerSeries_C]; rfl

theorem smul_eq (c : k) (x : k⸨X⸩) : c • x = algebraMap k k⸨X⸩ c * x := by rw [algebraMap_eq, HahnSeries.C_mul_eq_smul]

instance towerA : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun c x y => by
  rw [smul_eq, smul_eq k c, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerB : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun c a y => by
  rw [smul_eq k c, Algebra.smul_def (c • a), Algebra.smul_def a, Algebra.smul_def c, map_mul, mul_assoc]
  rfl⟩

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by unfold vv; exact (HahnSeries.ofPowerSeries_X).symm

theorem vv_ne : vv k ≠ 0 := by unfold vv; exact HahnSeries.single_ne_zero one_ne_zero

def inv1 (c : k) : k⟦X⟧ := PowerSeries.invOfUnit (1 + PowerSeries.C c * PowerSeries.X) 1

theorem powerSeries_oneAddConstMulX_mul_inv (c : k) : (1 + PowerSeries.C c * PowerSeries.X) * inv1 k c = 1 := by unfold inv1; exact PowerSeries.mul_invOfUnit _ _ (by simp)

theorem hs (c : k) : PowerSeries.HasSubst (PowerSeries.X * inv1 k c : k⟦X⟧) := PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

def sb (c : k) : k⟦X⟧ →ₐ[k] k⟦X⟧ := PowerSeries.substAlgHom (hs k c)

theorem sb_X (c : k) : sb k c PowerSeries.X = PowerSeries.X * inv1 k c := PowerSeries.substAlgHom_X _

theorem sb_C (c d : k) : sb k c (PowerSeries.C d) = PowerSeries.C d := by
  rw [← mul_one (PowerSeries.C d), ← PowerSeries.smul_eq_C_mul, map_smul, map_one]

theorem sb_key (c : k) : sb k c (PowerSeries.X * inv1 k (-c)) = PowerSeries.X := by
  have hv := powerSeries_oneAddConstMulX_mul_inv k c
  have hs0 := congrArg (sb k c) (powerSeries_oneAddConstMulX_mul_inv k (-c))
  simp only [map_mul, map_add, map_one, sb_C, sb_X, map_neg] at hs0
  rw [map_mul, sb_X]
  linear_combination (PowerSeries.X * inv1 k c * PowerSeries.C c * PowerSeries.X * sb k c (inv1 k (-c))
      + PowerSeries.X) * hv + PowerSeries.X * inv1 k c * (1 + PowerSeries.C c * PowerSeries.X) * hs0

theorem sb_sb (c : k) (f : k⟦X⟧) : sb k c (sb k (-c) f) = f := by
  have h := sb_key k c
  simp only [sb, PowerSeries.coe_substAlgHom] at h ⊢
  rw [PowerSeries.subst_comp_subst_apply (hs k (-c)) (hs k c), h, PowerSeries.X_subst]

def sbE : k⟦X⟧ ≃+* k⟦X⟧ :=
  RingEquiv.ofBijective (sb k 1).toRingHom
    ⟨Function.LeftInverse.injective (g := sb k (-1)) (fun f => by simpa using sb_sb k (-1) f),
     Function.RightInverse.surjective (g := sb k (-1)) (fun f => sb_sb k 1 f)⟩

def gE : k⸨X⸩ ≃+* k⸨X⸩ := IsFractionRing.ringEquivOfRingEquiv (A := k⟦X⟧) (B := k⟦X⟧) (sbE k)

theorem gE_coe (a : k⟦X⟧) : gE k (a : k⸨X⸩) = ((sb k 1 a : k⟦X⟧) : k⸨X⸩) := IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := k⸨X⸩) (L := k⸨X⸩) (sbE k) a

def gA : k⸨X⸩ →ₐ[k] k⸨X⸩ :=
  { (gE k).toRingHom with
    commutes' := fun c => by
      change gE k ((algebraMap k k⟦X⟧ c : k⟦X⟧) : k⸨X⸩) = ((algebraMap k k⟦X⟧ c : k⟦X⟧) : k⸨X⸩)
      rw [gE_coe, AlgHom.commutes] }

end

section
variable {k : Type} [Field k]

def lin (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun := σ
  map_add' := map_add σ
  map_smul' c x := by simp only [smul_eq, map_mul, AlgHom.commutes, RingHom.id_apply]

def lat (k : Type) [Field k] (a : ℤ) : Submodule k⟦X⟧ k⸨X⸩ := Submodule.span k⟦X⟧ {vv k ^ a}

theorem mem_lat {a : ℤ} {y : k⸨X⸩} : y ∈ lat k a ↔ ∃ b : k⟦X⟧, (b : k⸨X⸩) * vv k ^ a = y := by
  unfold lat
  rw [Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, LaurentSeries.coe_algebraMap]

theorem nab_apply (g : k⸨X⸩ →ₗ[k] k⸨X⸩) (y : k⸨X⸩) : nab g y = (vv k)⁻¹ * (g y - y) := rfl

theorem sb_sub (a : k⟦X⟧) : ∃ b : k⟦X⟧, sb k 1 a - a = PowerSeries.X * b := by
  refine ⟨inv1 k 1 * sb k 1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a)
    - PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a, ?_⟩
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  rw [map_add, map_mul, sb_X, sb_C]
  ring

theorem nab_coe (a : k⟦X⟧) : ∃ b : k⟦X⟧, nab (lin (gA k)) (a : k⸨X⸩) = b := by
  obtain ⟨b, hb⟩ := sb_sub a
  refine ⟨b, ?_⟩
  rw [nab_apply]
  change (vv k)⁻¹ * (gE k (a : k⸨X⸩) - (a : k⸨X⸩)) = _
  rw [gE_coe, show ((sb k 1 a : k⟦X⟧) : k⸨X⸩) - (a : k⸨X⸩) = ((sb k 1 a - a : k⟦X⟧) : k⸨X⸩) from
    (map_sub _ _ _).symm, hb, map_mul, ← vv_eq, inv_mul_cancel_left₀ (vv_ne k)]

theorem g_vinv : gE k (vv k)⁻¹ = (vv k)⁻¹ + 1 := by
  have h1 : gE k (vv k) = vv k * ((inv1 k 1 : k⟦X⟧) : k⸨X⸩) := by
    rw [vv_eq, gE_coe, sb_X, map_mul]
  have h2 : ((1 + PowerSeries.X : k⟦X⟧) : k⸨X⸩) * ((inv1 k 1 : k⟦X⟧) : k⸨X⸩) = 1 := by
    rw [← map_mul, ← map_one (HahnSeries.ofPowerSeries ℤ k)]
    congr 1
    simpa using powerSeries_oneAddConstMulX_mul_inv k 1
  have h3 : ((1 + PowerSeries.X : k⟦X⟧) : k⸨X⸩) = 1 + vv k := by rw [map_add, map_one, vv_eq]
  rw [h3] at h2
  rw [map_inv₀, h1, mul_inv, ← eq_inv_of_mul_eq_one_left h2, mul_add, mul_one,
    inv_mul_cancel₀ (vv_ne k)]

theorem nab_vinv : nab (lin (gA k)) (vv k)⁻¹ = (vv k)⁻¹ := by
  rw [nab_apply]
  change (vv k)⁻¹ * (gE k (vv k)⁻¹ - (vv k)⁻¹) = _
  rw [g_vinv, add_sub_cancel_left, mul_one]

theorem coe_mem (b : k⟦X⟧) : (b : k⸨X⸩) ∈ lat k (-1) := mem_lat.mpr ⟨PowerSeries.X * b, by
  rw [map_mul, ← vv_eq, zpow_neg_one, mul_comm (vv k), mul_inv_cancel_right₀ (vv_ne k)]⟩

theorem step (x c : k) (b : k⟦X⟧) : ∃ b' : k⟦X⟧,
    (nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) (c • (vv k)⁻¹ + b)
      = ((1 - x) * c) • (vv k)⁻¹ + b' := by
  obtain ⟨b₁, hb₁⟩ := nab_coe (k := k) b
  refine ⟨b₁ - PowerSeries.C x * b, ?_⟩
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply, map_add, map_smul, nab_vinv, hb₁]
  simp only [smul_eq k, algebraMap_eq, map_sub, map_mul, map_one, HahnSeries.ofPowerSeries_C]
  ring

theorem steps (x : k) (m : ℕ) : ∀ (c : k) (b : k⟦X⟧), ∃ b' : k⟦X⟧,
    ((nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) ^ m) (c • (vv k)⁻¹ + b)
      = ((1 - x) ^ m * c) • (vv k)⁻¹ + b' := by
  induction m with
  | zero => intro c b; exact ⟨b, by simp⟩
  | succ m ih =>
    intro c b
    obtain ⟨b₁, hb₁⟩ := step x c b
    obtain ⟨b₂, hb₂⟩ := ih ((1 - x) * c) b₁
    refine ⟨b₂, ?_⟩
    rw [pow_succ, Module.End.mul_apply, hb₁, hb₂, pow_succ, mul_assoc]

end

section
variable {k : Type} [Field k]

theorem gmult_top_bot {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (x : k) :
    gmult T ⊤ ⊥ x = Module.finrank k (T.maxGenEigenspace x) := by
  have hS : (⨆ m : ℕ, (⊥ : Submodule k U).comap ((T - algebraMap k (Module.End k U) x) ^ m))
      = T.maxGenEigenspace x := by
    apply le_antisymm
    · refine iSup_le fun m y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one] at hy
      exact (Module.End.mem_maxGenEigenspace T x y).mpr ⟨m, hy⟩
    · intro y hy
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T x y).mp hy
      refine Submodule.mem_iSup_of_mem m ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one]
      exact hm
  unfold gmult
  rw [top_inf_eq, hS]
  have hb : (⊥ : Submodule k U).submoduleOf (T.maxGenEigenspace x) = ⊥ := by
    ext y
    simp [Submodule.submoduleOf]
  rw [hb]
  exact (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

end

end GlobalTheory.PhiGam.Model

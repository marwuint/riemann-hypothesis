import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH
open Classical

section Form

variable {g n : ℕ}

theorem eStd_add_left (a a' b : Fin g ⊕ Fin g → ZMod n) : eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_add_right (a b b' : Fin g ⊕ Fin g → ZMod n) : eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_swap (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n b a = -eStd g n a b := by
  simp only [eStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem eStd_self (a : Fin g ⊕ Fin g → ZMod n) : eStd g n a a = 0 :=
  Finset.sum_eq_zero fun i _ => by ring

@[simp] theorem eStd_zero_left (b : Fin g ⊕ Fin g → ZMod n) : eStd g n 0 b = 0 := by simp [eStd]

@[simp] theorem eStd_zero_right (a : Fin g ⊕ Fin g → ZMod n) : eStd g n a 0 = 0 := by simp [eStd]

theorem eStd_neg_left (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n (-a) b = -eStd g n a b := by
  simp only [eStd, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_neg_right (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a (-b) = -eStd g n a b := by
  rw [eStd_swap, eStd_neg_left, neg_neg, eStd_swap]

def eStdBilin (g n : ℕ) : LinearMap.BilinForm (ZMod n) (Fin g ⊕ Fin g → ZMod n) :=
  LinearMap.mk₂ (ZMod n) (eStd g n) eStd_add_left
    (fun c a b => by
      simp only [eStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    eStd_add_right
    (fun c a b => by
      simp only [eStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

@[simp] theorem eStdBilin_apply (a b : Fin g ⊕ Fin g → ZMod n) : eStdBilin g n a b = eStd g n a b := rfl

theorem eStd_single_inr (a : Fin g ⊕ Fin g → ZMod n) (i : Fin g) :
    eStd g n a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [eStd, Pi.single_apply]

theorem eStd_single_inl (a : Fin g ⊕ Fin g → ZMod n) (i : Fin g) :
    eStd g n a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [eStd, Pi.single_apply]

theorem eq_zero_of_eStd_eq_zero {a : Fin g ⊕ Fin g → ZMod n} (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext k
  rcases k with i | i
  · exact (eStd_single_inr a i).symm.trans (h _)
  · exact neg_eq_zero.1 ((eStd_single_inl a i).symm.trans (h _))

theorem eStdBilin_bijective : Function.Bijective (eStdBilin g n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a h => eq_zero_of_eStd_eq_zero fun b => LinearMap.congr_fun h b,
    fun f => ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)), ?_⟩⟩
  refine (Pi.basisFun (ZMod n) _).ext fun k => ?_
  rcases k with i | i
  · simp [eStd_single_inl]
  · simp [eStd_single_inr]

end Form

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance instNeZeroExponent : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance instNeZeroLevel : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne S.N)⟩

instance instNeZeroLevelSq : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩

variable {S}

theorem mem_perp {H : AddSubgroup S.Gam} {a : S.Gam} : a ∈ S.perp H ↔ ∀ h ∈ H, eStd S.g _ a h = 0 := Iff.rfl

theorem mem_perp' {H : AddSubgroup S.Gam} {a : S.Gam} : a ∈ S.perp H ↔ ∀ h ∈ H, eStd S.g _ h a = 0 :=
  forall₂_congr fun h _ => by rw [eStd_swap a h, neg_eq_zero]

theorem perp_anti {H H' : AddSubgroup S.Gam} (h : H ≤ H') : S.perp H' ≤ S.perp H :=
  fun _ ha x hx => ha x (h hx)

theorem le_perp_comm {H H' : AddSubgroup S.Gam} : H ≤ S.perp H' ↔ H' ≤ S.perp H :=
  ⟨fun h _ hx => mem_perp'.2 fun _ ha => h ha _ hx, fun h _ hx => mem_perp'.2 fun _ ha => h ha _ hx⟩

theorem le_perp_perp (H : AddSubgroup S.Gam) : H ≤ S.perp (S.perp H) := le_perp_comm.1 le_rfl

variable (S)

@[simp] theorem perp_bot : S.perp ⊥ = ⊤ := top_unique (le_perp_comm.1 bot_le)

@[simp] theorem perp_top : S.perp ⊤ = ⊥ :=
  bot_unique fun _ ha => eq_zero_of_eStd_eq_zero fun b => ha b trivial

@[simp] theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  have h := (GlobalTheory.orthogonal_free_of_perfect_alt_zmod S.N S.r S.Gam (eStdBilin _ _) eStd_self
    eStdBilin_bijective).1 (AddSubgroup.toZModSubmodule _ H)
  refine le_antisymm (fun a ha => ?_) (le_perp_perp H)
  have h1 : a ∈ (eStdBilin S.g _).orthogonal ((eStdBilin S.g _).orthogonal (AddSubgroup.toZModSubmodule _ H)) :=
    fun b hb => mem_perp'.1 ha b (mem_perp'.2 hb)
  rwa [h] at h1

theorem bot_isoFree : S.IsoFree ⊥ := ⟨bot_le, 0, ⟨AddEquiv.ofUnique⟩⟩

theorem prim_ζN : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (by ring)

def psi : AddChar (ZMod S.N) o := AddChar.zmodChar S.N S.prim_ζN.pow_eq_one

theorem psi_apply (a : ZMod S.N) : S.psi a = S.ζN ^ a.val := rfl

instance finite_hom (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) := DFunLike.finite _

@[simp] theorem ρ_zero : S.ρ 0 = 1 := S.ρ_one 0 (smul_zero _)

theorem proj_eq_one_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) (c : T →+ ZMod S.N) : S.proj T c = 1 := by
  subst h
  rw [proj, finsum_unique, AddSubgroup.card_bot, Subsingleton.elim (default : (⊥ : AddSubgroup S.Gam)) 0]
  simp

variable {S}

variable (S)

theorem FF_mem (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    S.FF T c k ∈ S.R := by
  have := Fintype.ofFinite T
  rw [FF, finsum_eq_sum_of_fintype]
  exact sum_mem fun t _ => mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem map_FF {K : Type} [CommRing K] (y : S.R →+* K) (T : AddSubgroup S.Gam) [Fintype T] (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) (hk : S.FF T c k ∈ S.R) :
    y ⟨S.FF T c k, hk⟩ = ∑ t : T, y (algebraMap o S.R S.ζ) ^ (k.2 t).val *
      ∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem t j⟩ := by
  simp only [← map_mul, ← map_sum, ← map_pow]
  congr 1
  apply Subtype.ext
  simp [FF, finsum_eq_sum_of_fintype]

theorem FF_eq_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k = algebraMap o Ω (S.ζ ^ (k.2 0).val) * S.ev 0 k.1 := by
  rw [FF, S.proj_eq_one_of_eq_bot h]
  subst h
  rw [finsum_unique, Subsingleton.elim (default : (⊥ : AddSubgroup S.Gam)) 0]
  simp [Matrix.one_apply]

theorem norm_ζ {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p) : ‖y (algebraMap o S.R S.ζ)‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne ((S.r * S.N) ^ 2))).1 ?_
  rw [← norm_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, norm_one]

namespace Test

variable {S} {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)

theorem q_pos {α : τ.X} (h : α ≠ 0) : 0 < τ.q α := by
  have hinj : Function.Injective fun n : ℤ => n • α := smul_left_injective ℤ h
  obtain ⟨n, hn⟩ := ((τ.pos.comp hinj.tendsto_cofinite).eventually_gt_atTop 0).exists
  rw [Function.comp_apply, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  by_contra h0
  nlinarith [mul_self_nonneg (n : ℝ)]

theorem q_nonneg (α : τ.X) : 0 ≤ τ.q α := by
  rcases eq_or_ne α 0 with rfl | h
  · rw [map_zero]
  · exact (τ.q_pos h).le

theorem exists_shortest (β : τ.X) : ∃ v : τ.X, ∀ v0, τ.q (β + S.N • v) ≤ τ.q (β + S.N • v + S.N • v0) := by
  have hinj : Function.Injective fun v : τ.X => β + S.N • v := fun v w h =>
    smul_right_injective τ.X (r := (S.N : ℤ)) (Int.natCast_ne_zero.2 (NeZero.ne S.N)) (by simpa using h)
  obtain ⟨v, hv⟩ := (τ.pos.comp hinj.tendsto_cofinite).exists_forall_le
  exact ⟨v, fun v0 => by simpa only [Function.comp_apply, smul_add, add_assoc] using hv (v + v0)⟩

@[simp] theorem wt_nsmul (v : τ.X) : τ.wt (S.N • v) = 0 := by
  ext t
  rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddMonoidHom.zero_apply]

theorem perp_ker_le_ker : S.perp τ.yy.ker ≤ τ.yy.ker := τ.isoFree.1.trans (S.perp_perp _).le

theorem δ_eq (τ' : S.Test p y) : τ.δ = τ'.δ := τ.δ_max.unique τ'.δ_max

end Test

variable (M : RatModel o Ω)

@[simp] theorem perp_TT (z : M.Z) : S.perp (S.TT M z) = S.HH M z := S.perp_perp _

theorem supI_mono {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ := fun _ hx => RatModel.Div.of_specializes hx h

theorem HH_mono {ξ z : M.Z} (h : ξ ⤳ z) : S.HH M z ≤ S.HH M ξ := AddSubgroup.closure_mono (S.supI_mono M h)

theorem TT_anti {ξ z : M.Z} (h : ξ ⤳ z) : S.TT M ξ ≤ S.TT M z := perp_anti (S.HH_mono M h)

theorem TT_genericPoint : S.TT M (genericPoint M.Z) = ⊥ := by
  have h : S.supI M (genericPoint M.Z) = {x | S.th x ≠ 0} :=
    Set.ext fun _ => ⟨fun h => h.1, fun h => RatModel.div_genericPoint h⟩
  rw [TT, HH, h, S.supp, perp_top]

end ThetaSys

theorem ArithBase.isDomain (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] : IsDomain o :=
  h.inj.isDomain

theorem ArithBase.charZero (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] : CharZero o :=
  have := h.char
  (algebraMap o Ω).charZero

instance : ArithBase ℤ ℚ := ⟨inferInstance, inferInstance, inferInstance, IsFractionRing.injective ℤ ℚ⟩

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

def Test.good {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p) (δ : ℝ)
    (hmax : IsGreatest (Set.range fun x => ‖y ⟨S.th x, S.th_mem x⟩‖) δ) (hpos : 0 < δ)
    (hsupp : AddSubgroup.closure {x | ‖y ⟨S.th x, S.th_mem x⟩‖ = δ} = ⊤)
    (hev : ∀ h, IsGreatest (Set.range fun i => ‖y ⟨S.ev h i, S.ev_mem h i⟩‖) δ) : S.Test p y :=
  have hT : S.perp (0 : S.Gam →+ PUnit ⧸ (nsmulAddMonoidHom (S.r * S.N) : PUnit →+ PUnit).range).ker = ⊥ := by
    rw [AddMonoidHom.ker_zero, perp_top]
  have hs : ∀ c h i, ∑ j, y (algebraMap o S.R (S.proj _ c j i)) * y ⟨S.ev h j, S.ev_mem h j⟩ =
      y ⟨S.ev h i, S.ev_mem h i⟩ := fun c h i => by
    rw [S.proj_eq_one_of_eq_bot hT]
    simp [Matrix.one_apply, apply_ite]
  { X := PUnit
    q := 0
    pos := by
      rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
    yy := 0
    yy_onto := fun a => ⟨0, by
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
      rfl⟩
    isoFree := hT ▸ S.bot_isoFree
    wt := 0
    wt_eq := fun x α _ t => by
      rw [(AddSubgroup.mem_bot.1 (hT.le t.2) : (t : S.Gam) = 0), eStd_zero_left]
      exact (map_zero _).symm
    δ := δ
    δ_max := hmax
    δ_pos := hpos
    supp := hsupp.trans AddMonoidHom.ker_zero.symm
    tx := fun x _ => ⟨0, rfl, by simpa using hmax.2 ⟨x, rfl⟩⟩
    le := fun α _ h _ i => by
      rw [hs]
      simpa using (hev h).2 ⟨i, rfl⟩
    eq := fun α _ => by
      obtain ⟨i, hi⟩ := (hev 0).1
      refine ⟨(i, 0), S.FF_mem _ _ _, ?_⟩
      simp only [S.FF_eq_of_eq_bot hT]
      simpa using hi
    unit0 := fun h _ => by
      obtain ⟨i, hi⟩ := (hev h).1
      exact ⟨i, by rw [hs]; exact hi⟩ }

theorem exists_at_of_cen (M : RatModel o Ω) {U₀ : M.Z.Opens} (hle : S.R ≤ M.ringOn U₀) {z : M.Z} {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ z y) :
    ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  have hw : S.R ≤ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint _)) :=
    fun x hx => RatModel.mem_ringOn.1 (hle hx) _ (hc.2 ⟨_, rfl⟩)
  exact ⟨(RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ _)).comp (Subalgebra.inclusion hw).toRingHom,
    fun _ => rfl, fun a => hc.norm_val_le_one ((M.O z).algebraMap_mem a)⟩

end ThetaSys

section Heisenberg

variable {o : Type} [CommRing o] {N : ℕ} [NeZero N] (ψ : AddChar (ZMod N) o)

def heisMat (h u v : ZMod N) : Matrix (ZMod N) (ZMod N) o :=
  Matrix.of fun i j => if j = i + u then ψ (v * (i + h * u)) else 0

theorem heisMat_mul {h : ZMod N} (hh : 2 * h = 1) (u v u' v' : ZMod N) :
    heisMat ψ h u v * heisMat ψ h u' v' = ψ (h * (u * v' - v * u')) • heisMat ψ h (u + u') (v + v') := by
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (i + u) (fun j _ hj => by simp [heisMat, hj]) (by simp)]
  simp only [heisMat, Matrix.of_apply, if_true, Matrix.smul_apply, smul_eq_mul, add_assoc]
  split_ifs
  · rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination (-(u * v')) * hh
  · simp

end Heisenberg

section Inhabitants

variable {o : Type} (Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsFractionRing o Ω]

variable (o) in

theorem exists_eq_div_bot (x : Ω) : ∃ a ∈ (⊥ : Subalgebra o Ω), ∃ b ∈ (⊥ : Subalgebra o Ω), x = a / b := by
  obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective o x
  exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, h.symm⟩

variable {r N : ℕ} (hN : 2 ≤ N) (hr : 1 ≤ r) {ζ : o} (hζ : IsPrimitiveRoot ζ ((r * N) ^ 2))
  (hu : IsUnit ((r * N : ℕ) : o))

variable (hodd : Odd N) (ϖ : o) (hϖ : ϖ ≠ 0)

end Inhabitants

section Away

open NumberField

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev AwayBase : Type := Localization.Away (n : 𝓞 K)

namespace AwayBase

variable [NeZero n]

theorem powers_le : Submonoid.powers (n : 𝓞 K) ≤ nonZeroDivisors _ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 (NeZero.ne n))

theorem injective : Function.Injective (algebraMap (𝓞 K) (AwayBase K n)) :=
  IsLocalization.injective _ (powers_le K n)

instance instIsDomain : IsDomain (AwayBase K n) := IsLocalization.isDomain_localization (powers_le K n)

instance instIsDedekindDomain : IsDedekindDomain (AwayBase K n) :=
  IsLocalization.isDedekindDomain _ (powers_le K n) _

instance instCharZero : CharZero (AwayBase K n) := charZero_of_injective_algebraMap (injective K n)

omit [NeZero n] in

theorem finiteType : Algebra.FiniteType ℤ (AwayBase K n) :=
  Algebra.FiniteType.trans (S := 𝓞 K) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (n : 𝓞 K)) (AwayBase K n))

instance instArithBase : ArithBase (AwayBase K n) (FractionRing (AwayBase K n)) :=
  ⟨inferInstance, by convert finiteType K n using 1 <;> first | rfl | exact Subsingleton.elim _ _, inferInstance,
    IsFractionRing.injective _ _⟩

omit [NumberField K] [NeZero n] in

theorem isUnit_natCast : IsUnit (n : AwayBase K n) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := AwayBase K n) (n : 𝓞 K)
  rwa [map_natCast] at this

end AwayBase

end Away

end GlobalTheory.ZH
end

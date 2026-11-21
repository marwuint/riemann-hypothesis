import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

structure BKDat (η H : ℕ) extends PhiMod O K l e a ι where

  desc : Descent toPhiMod
  nabla_mem : ∀ m ∈ toPhiMod.MM, toPhiMod.nabla m ∈ toPhiMod.MM
  EN_mem : ∀ m ∈ toPhiMod.M, toPhiMod.EN m ∈ toPhiMod.Man
  lower : ∀ m ∈ toPhiMod.M, E K l e ^ H • m ∈ toPhiMod.L
  upper : ∀ m ∈ toPhiMod.L, E K l e ^ η • m ∈ toPhiMod.M

section RankOne

variable {O K l e a}

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem Ezpow_mem_A {i : ℤ} (hi : 0 ≤ i) : Ezpow K l e i ∈ A O K := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [Ezpow_natCast]
  exact pow_mem (E_mem l e _) n

variable [CompleteSpace K]

end RankOne

variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}

abbrev BKHom (D : BKDat O K l e a ι η H) (D' : BKDat O K l e a κ η' H') : Type :=
  Descent.Hom D.desc D'.desc

namespace BKDat

variable (D : BKDat O K l e a ι η H)

abbrev Y : Submodule O (Vec K a ι) := D.desc.Y η

abbrev Y' : Submodule O (Vec K a ι) := D.desc.Y' η

abbrev Yl : Submodule O (Vec K a ι) := D.desc.Yl η

abbrev Minv : Submodule O (Vec K a ι) := D.desc.Minv

abbrev Z : Submodule O D.Pol := D.desc.Z η

abbrev Zl : Submodule K D.Pol := D.desc.Zl η

structure IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) : Prop where
  chars_subset : ∀ τ, D.desc.chars τ ⊆ Sig
  jumps_subset : D.jumps ⊆ U

omit [NeZero e] in

theorem exists_conn_eq {m : Vec K a ι} (hm : m ∈ D.MM) : ∃ w ∈ D.MM, D.conn m = (X : K⟦X⟧) • w :=
  ⟨_, D.nabla_mem m hm, rfl⟩

omit [NeZero e] in
theorem conn_mem_MM {m : Vec K a ι} (hm : m ∈ D.MM) : D.conn m ∈ D.MM :=
  D.MM.smul_mem (uIn (S O K e)) (D.nabla_mem m hm)

theorem EN_mem_Man {m : Vec K a ι} (hm : m ∈ D.Man) : D.EN m ∈ D.Man :=
  D.EN_mem_Man_of_basis (fun i => D.EN_mem _ (D.bas_mem_M i)) hm

theorem EN_mem_divE {n : ℕ} {y : Vec K a ι} (hy : y ∈ divE l e n D.Man) :
    D.EN y ∈ divE l e n D.Man := by
  rw [mem_divE, D.E_pow_smul_EN]
  exact sub_mem (D.EN_mem_Man hy) (D.smul_mem_Man
    (mul_mem (natCast_mem _ n) (N_mem (derivative_mem_R l (E_mem l e _)))) hy)

omit [NeZero e] in

theorem smul_mem_Mext {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ D.ext B) :
    E K l e ^ η • m ∈ D.Mext B :=
  D.smul_mem_Mext_of_basis (fun i => D.upper _ (D.phi_mem_L (D.bas_mem_M i))) hB hm

def Lc : Module.End K D.Pol := D.Man.mapQ D.Man D.EN fun _ => D.EN_mem_Man

@[simp] theorem Lc_cls (v : Vec K a ι) : D.Lc (D.cls v) = D.cls (D.EN v) := rfl

theorem Lc_mem_PolEta {n : ℕ} {w : D.Pol} (hw : w ∈ D.PolEta n) : D.Lc w ∈ D.PolEta n := by
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨_, D.EN_mem_divE hy, rfl⟩

theorem actPol_Lc (g : TameGal K l e a) (w : D.Pol) :
    D.desc.actPol g (D.Lc w) = D.Lc (D.desc.actPol g w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Descent.actPol_cls, Descent.actPol_cls, Lc_cls, Descent.act_EN]

theorem Lc_mem_Zl {w : D.Pol} (hw : w ∈ D.Zl) : D.Lc w ∈ D.Zl :=
  ⟨D.Lc_mem_PolEta hw.1, fun g => by rw [actPol_Lc, hw.2 g]⟩

def LcZ : Module.End K D.Zl := D.Lc.restrict fun _ => D.Lc_mem_Zl

@[simp] theorem coe_LcZ (w : D.Zl) : (D.LcZ w : D.Pol) = D.Lc w := rfl

theorem Mon_eq (y : Vec K a ι) : D.Mon y = D.Lc (D.cls y) - D.cls (E K l e • D.zeta y) := by
  rw [PhiMod.Mon_apply, map_sub, Lc_cls]

theorem Mon_add_phi_sub (y : Vec K a ι) {m : Vec K a ι} (hm : m ∈ D.Man) :
    D.Mon (y + (D.phi m - m)) = D.Mon y := by
  rw [map_add, PhiMod.Mon_phi_sub, D.cls_eq_zero_iff.2 (D.EN_mem_Man hm), neg_zero, add_zero]

theorem _root_.GlobalTheory.BK.BKHom.onPol_Lc {D : BKDat O K l e a ι η H} {D' : BKDat O K l e a κ η' H'}
    (F : BKHom D D') (w : D.Pol) : F.onPol (D.Lc w) = D'.Lc (F.onPol w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Hom.onPol_cls, Hom.onPol_cls, Lc_cls, Hom.app_EN]

variable {D} {y : Vec K a ι}

omit [NeZero e] in
theorem mem_invE_of_mem_Y (hy : y ∈ D.Y) : y ∈ D.Mext (invE l e (A O K)) :=
  D.mem_Mext_invE_of_mem_divE hy.1

end BKDat

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

def avg : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (TameGal K l e a)
  ((Nat.card (TameGal K l e a) : K)⁻¹) • ∑ g, Δ.act g

omit [IsUltrametricDist K] in
theorem norm_card : ‖(Nat.card (TameGal K l e a) : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 TameGal.not_dvd_card

theorem avg_mem_inv (v : Vec K a ι) : Δ.avg v ∈ Δ.inv := fun g => by
  let _ := Fintype.ofFinite (TameGal K l e a)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  exact congrArg _ (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl)

theorem map_avg {V : Type} [AddCommGroup V] [Module K V] (f : Vec K a ι →ₗ[K] V) {v : Vec K a ι}
    (h : ∀ g, f (Δ.act g v) = f v) : f (Δ.avg v) = f v := by
  let _ := Fintype.ofFinite (TameGal K l e a)
  have h0 : (Nat.card (TameGal K l e a) : K) ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_card]; simp)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, inv_smul_smul₀ h0]

theorem avg_mem (W : Submodule O (Vec K a ι)) {v : Vec K a ι} (h : ∀ g, Δ.act g v ∈ W) :
    Δ.avg v ∈ W := by
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) ((Nat.card (TameGal K l e a) : K)⁻¹)).2
    (by rw [norm_inv, norm_card, inv_one])
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (W.sum_mem fun g _ => h g)

theorem map_Y (η : ℕ) : (Δ.Y η).map (P.cls.restrictScalars O) = Δ.Z η := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact Δ.cls_mem_Z hy
  · obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
    exact ⟨Δ.avg y, ⟨Δ.avg_mem _ fun g => Δ.act_mem_EM g hy, Δ.avg_mem_inv y⟩, Δ.map_avg P.cls h⟩

end Descent

section Examples

omit [NeZero a] [TameDescentExponentData K l e a]

theorem Ezpow_mem_invL_A_iff {i : ℤ} : Ezpow K l e i ∈ invL l (A O K) ↔ 0 ≤ i := by
  refine ⟨fun h => not_lt.1 fun hi => ?_, fun h => le_away (A O K) _ (Ezpow_mem_A h)⟩
  have h0 : Ezpow K l e (-1 - i) ∈ invL l (A O K) := le_away _ _ (Ezpow_mem_A (by omega))
  have h1 := mul_mem h0 h
  rw [← Ezpow_add, sub_add_cancel] at h1
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : Ezpow K l e (-1) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e h1) fun n => by
    rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
  exact Units.ne_zero _ h3

end Examples

end GlobalTheory.BK

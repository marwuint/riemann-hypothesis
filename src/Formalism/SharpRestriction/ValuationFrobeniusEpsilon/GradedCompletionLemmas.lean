import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

noncomputable section

namespace Formalism.MainNotions.UnusedSlot38
open Formalism.BasicNotions.V1 IsLocalRing MvPowerSeries Filter
open scoped Classical

open MvPowerSeries IsLocalRing Filter

section Graded

variable {O : Type} [CommRing O] {a rk : ℕ} (wt : Fin a → (Fin rk → ℤ))

def monoWt (m : Fin a →₀ ℕ) : Fin rk → ℤ := m.sum fun i e => (e : ℤ) • wt i

theorem monoWt_add (m m' : Fin a →₀ ℕ) : monoWt wt (m + m') = monoWt wt m + monoWt wt m' := by
  unfold monoWt
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i e e'; push_cast; exact add_smul _ _ _

theorem monoWt_zero : monoWt wt (0 : Fin a →₀ ℕ) = 0 := by simp [monoWt]

theorem monoWt_single (i : Fin a) : monoWt wt (Finsupp.single i 1) = wt i := by
  simp [monoWt]

variable (O) in

def Pj (j : Fin rk → ℤ) : Submodule O (MvPowerSeries (Fin a) O) where
  carrier := {f | ∀ m, coeff m f ≠ 0 → monoWt wt m = j}
  add_mem' {f g} hf hg m h := by
    rw [map_add] at h
    by_cases h1 : coeff m f = 0
    · rw [h1, zero_add] at h; exact hg m h
    · exact hf m h1
  zero_mem' m h := by simp at h
  smul_mem' c f hf m h := by
    rw [map_smul, smul_eq_mul] at h
    exact hf m (right_ne_zero_of_mul h)

theorem Pj_mul {i j : Fin rk → ℤ} {f g : MvPowerSeries (Fin a) O} (hf : f ∈ Pj O wt i)
    (hg : g ∈ Pj O wt j) : f * g ∈ Pj O wt (i + j) := by
  intro m hm
  classical
  rw [coeff_mul] at hm
  obtain ⟨⟨p, q⟩, hpq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hpq' : p + q = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
  rw [← hpq', monoWt_add, hf p (left_ne_zero_of_mul hne), hg q (right_ne_zero_of_mul hne)]

theorem one_mem_degree_zero : (1 : MvPowerSeries (Fin a) O) ∈ Pj O wt 0 := by
  classical
  intro m hm
  rw [coeff_one] at hm
  split_ifs at hm with h
  · rw [h, monoWt_zero]
  · exact absurd rfl hm

theorem algebraMap_mem_degree_zero (c : O) : algebraMap O (MvPowerSeries (Fin a) O) c ∈ Pj O wt 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (Pj O wt 0).smul_mem c (one_mem_degree_zero wt)

theorem X_mem_Pj (i : Fin a) : (X i : MvPowerSeries (Fin a) O) ∈ Pj O wt (wt i) := by
  classical
  intro m hm
  rw [coeff_X] at hm
  split_ifs at hm with h
  · rw [h, monoWt_single]
  · exact absurd rfl hm

variable (O) in

def Psub : Subalgebra O (MvPowerSeries (Fin a) O) where
  carrier := ((⨆ j, Pj O wt j : Submodule O (MvPowerSeries (Fin a) O)) : Set _)
  mul_mem' {x y} hx hy := by
    simp only [SetLike.mem_coe] at hx hy ⊢
    refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ ⨆ j, Pj O wt j) hx ?_ ?_ ?_
    · intro i x hx
      refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ ⨆ j, Pj O wt j) hy ?_ ?_ ?_
      · intro j y hy; exact Submodule.mem_iSup_of_mem (i + j) (Pj_mul wt hx hy)
      · simp
      · intro y y' h h'; rw [mul_add]; exact Submodule.add_mem _ h h'
    · simp
    · intro x x' h h'; rw [add_mul]; exact Submodule.add_mem _ h h'
  add_mem' hx hy := Submodule.add_mem _ hx hy
  algebraMap_mem' c := Submodule.mem_iSup_of_mem 0 (algebraMap_mem_degree_zero wt c)

variable (O) in

def P0sub : Subalgebra O (MvPowerSeries (Fin a) O) where
  carrier := (Pj O wt 0 : Set _)
  mul_mem' {x y} hx hy := by
    have := Pj_mul wt hx hy; rwa [add_zero] at this
  add_mem' hx hy := Submodule.add_mem _ hx hy
  algebraMap_mem' c := algebraMap_mem_degree_zero wt c

theorem degree_zero_le_graded : P0sub O wt ≤ Psub O wt := fun _ hx => Submodule.mem_iSup_of_mem 0 hx

theorem Pj_le_P (j : Fin rk → ℤ) {x : MvPowerSeries (Fin a) O} (hx : x ∈ Pj O wt j) :
    x ∈ Psub O wt :=
  Submodule.mem_iSup_of_mem j hx

def comp (j : Fin rk → ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  fun m => if monoWt wt m = j then coeff m f else 0

def IsHomog (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=
  ∀ f ∈ Jh, ∀ j, comp wt j f ∈ Jh

def IsClosedAdic [IsLocalRing O] (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=
  ∀ f, (∀ N : ℕ, f ∈ Jh ⊔ maximalIdeal (MvPowerSeries (Fin a) O) ^ N) → f ∈ Jh

def Jsub (Jh : Ideal (MvPowerSeries (Fin a) O)) : Submodule O (MvPowerSeries (Fin a) O) :=
  ⨆ j, Jh.restrictScalars O ⊓ Pj O wt j

abbrev mk (Jh : Ideal (MvPowerSeries (Fin a) O)) :
    MvPowerSeries (Fin a) O →ₐ[O] MvPowerSeries (Fin a) O ⧸ Jh :=
  Ideal.Quotient.mkₐ O Jh

variable (Jh : Ideal (MvPowerSeries (Fin a) O))

def Aj (j : Fin rk → ℤ) : Submodule O (MvPowerSeries (Fin a) O ⧸ Jh) :=
  (Pj O wt j).map (mk Jh).toLinearMap

def Asub : Subalgebra O (MvPowerSeries (Fin a) O ⧸ Jh) := (Psub O wt).map (mk Jh)

def A0sub : Subalgebra O (MvPowerSeries (Fin a) O ⧸ Jh) := (P0sub O wt).map (mk Jh)

theorem base_subalgebra_le : A0sub wt Jh ≤ Asub wt Jh := Subalgebra.map_mono (degree_zero_le_graded wt)

theorem Aj_le_A {j : Fin rk → ℤ} {y : MvPowerSeries (Fin a) O ⧸ Jh} (hy : y ∈ Aj wt Jh j) :
    y ∈ Asub wt Jh := by
  obtain ⟨f, hf, rfl⟩ := hy
  exact ⟨f, Pj_le_P wt j hf, rfl⟩

theorem mkX_mem_A (i : Fin a) : mk Jh (X i) ∈ Asub wt Jh :=
  ⟨X i, Pj_le_P wt (wt i) (X_mem_Pj wt i), rfl⟩

def mhat [IsLocalRing O] : Ideal (MvPowerSeries (Fin a) O ⧸ Jh) :=
  (maximalIdeal (MvPowerSeries (Fin a) O)).map (Ideal.Quotient.mk Jh)

def m0 [IsLocalRing O] : Ideal (A0sub wt Jh) := (mhat Jh).comap (A0sub wt Jh).val

end Graded

section Coh

variable {k : Type} [Field k] {n : ℕ}

def dC {H : Type} [Group H] (act : H → Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k)
    (m : ℕ) : ((Fin m → H) → Matrix (Fin n) (Fin n) k) →ₗ[k]
      ((Fin (m + 1) → H) → Matrix (Fin n) (Fin n) k) where
  toFun c x := act (x 0) (c fun i => x i.succ) + Finset.univ.sum fun j : Fin (m + 1) =>
    (-1 : k) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) x)
  map_add' c c' := by
    ext x
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r c := by
    funext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

def IsCoch {H : Type} [TopologicalSpace H] {m : ℕ} (N : Submodule k (Matrix (Fin n) (Fin n) k))
    (c : (Fin m → H) → Matrix (Fin n) (Fin n) k) : Prop :=
  IsLocallyConstant c ∧ ∀ x, c x ∈ N

def CochSub {H : Type} [TopologicalSpace H] (m : ℕ) (N : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Submodule k ((Fin m → H) → Matrix (Fin n) (Fin n) k) where
  carrier := {c | IsCoch N c}
  add_mem' {c c'} hc hc' := ⟨hc.1.add hc'.1, fun x => N.add_mem (hc.2 x) (hc'.2 x)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' a c hc := ⟨hc.1.comp (a • ·), fun x => N.smul_mem a (hc.2 x)⟩

end Coh

section Fib

variable (P : LiftProb)

abbrev kk : Type := ResidueField P.O

abbrev MM : Type := Matrix (Fin P.kind.n) (Fin P.kind.n) (kk P)

abbrev FA (m : ℕ) : Type :=
  ((Fin m → P.Gam) → MM P) × (∀ q, (Fin m → P.Gq q) → MM P) × (∀ v, (Fin m → P.Gv v) → MM P)

abbrev FB (m : ℕ) : Type := (∀ q, (Fin m → P.Gq q) → MM P) × (∀ v, (Fin m → P.Gv v) → MM P)

variable {P}

def resL (H : Subgroup P.Gam) (m : ℕ) : ((Fin m → P.Gam) → MM P) →ₗ[kk P] ((Fin m → H) → MM P) :=
  LinearMap.funLeft (kk P) (MM P) fun x i => (x i : P.Gam)

variable (act : P.Gam → MM P →ₗ[kk P] MM P)

def pG (m : ℕ) : FA P m →ₗ[kk P] ((Fin m → P.Gam) → MM P) := LinearMap.fst _ _ _
def pQ (m : ℕ) (q : P.qPl) : FA P m →ₗ[kk P] ((Fin m → P.Gq q) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun q : P.qPl => (Fin m → P.Gq q) → MM P) q).comp
    ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
def pV (m : ℕ) (v : P.lPl) : FA P m →ₗ[kk P] ((Fin m → P.Gv v) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun v : P.lPl => (Fin m → P.Gv v) → MM P) v).comp
    ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))
def qQ (m : ℕ) (q : P.qPl) : FB P m →ₗ[kk P] ((Fin m → P.Gq q) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun q : P.qPl => (Fin m → P.Gq q) → MM P) q).comp
    (LinearMap.fst _ _ _)
def qV (m : ℕ) (v : P.lPl) : FB P m →ₗ[kk P] ((Fin m → P.Gv v) → MM P) :=
  (LinearMap.proj (R := kk P) (φ := fun v : P.lPl => (Fin m → P.Gv v) → MM P) v).comp
    (LinearMap.snd _ _ _)

def dA (m : ℕ) : FA P m →ₗ[kk P] FA P (m + 1) :=
  LinearMap.prod ((dC act m).comp (pG m)) (LinearMap.prod
    (LinearMap.pi fun q => (dC (fun h : P.Gq q => act h) m).comp (pQ m q))
    (LinearMap.pi fun v => (dC (fun h : P.Gv v => act h) m).comp (pV m v)))

def dB (m : ℕ) : FB P m →ₗ[kk P] FB P (m + 1) :=
  LinearMap.prod
    (LinearMap.pi fun q => (dC (fun h : P.Gq q => act h) m).comp (qQ m q))
    (LinearMap.pi fun v => (dC (fun h : P.Gv v => act h) m).comp (qV m v))

variable {act}

def fAB (m : ℕ) : FA P m →ₗ[kk P] FB P m :=
  LinearMap.prod
    (LinearMap.pi fun q => (resL (P.Gq q) m).comp (pG m) - pQ m q)
    (LinearMap.pi fun v => (resL (P.Gv v) m).comp (pG m) - pV m v)

variable (act)

def d0 : FA P 0 →ₗ[kk P] FA P 1 × FB P 0 := LinearMap.prod (dA act 0) (fAB 0)

def dS (m : ℕ) : FA P (m + 1) × FB P m →ₗ[kk P] FA P (m + 2) × FB P (m + 1) :=
  LinearMap.prod ((dA act (m + 1)).comp (LinearMap.fst _ _ _))
    ((fAB (m + 1)).comp (LinearMap.fst _ _ _) - (dB act m).comp (LinearMap.snd _ _ _))

def NqSet (q : P.qPl) : Set P.Gam := {g | g ∈ P.Iq q ∧ g ∈ P.GF ∧ P.rbar g = 1}

variable (N : Submodule (kk P) (MM P)) (localization₂ : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop)

def AdmA (m : ℕ) : Set (FA P m) :=
  {x | IsCoch N x.1 ∧ (∀ q, IsCoch N (x.2.1 q) ∧ ∀ y z : Fin m → P.Gq q,
      (∀ i, ((y i : P.Gam))⁻¹ * (z i : P.Gam) ∈ NqSet q) → x.2.1 q y = x.2.1 q z) ∧
    ∀ v, IsCoch N (x.2.2 v) ∧ localization₂ v m (x.2.2 v)}

def AdmB (m : ℕ) : Set (FB P m) := {y | (∀ q, IsCoch N (y.1 q)) ∧ ∀ v, IsCoch N (y.2 v)}

def Z0 : Set (FA P 0) := {x | x ∈ AdmA N localization₂ 0 ∧ d0 act x = 0}

def Zs (m : ℕ) : Set (FA P (m + 1) × FB P m) :=
  {x | x.1 ∈ AdmA N localization₂ (m + 1) ∧ x.2 ∈ AdmB N m ∧ dS act m x = 0}

def Bd : (m : ℕ) → Set (FA P (m + 1) × FB P m)
  | 0 => d0 act '' AdmA N localization₂ 0
  | m + 1 => dS act m '' {x | x.1 ∈ AdmA N localization₂ (m + 1) ∧ x.2 ∈ AdmB N m}

def ZsS (m : ℕ) : Submodule (kk P) (FA P (m + 1) × FB P m) := Submodule.span (kk P) (Zs act N localization₂ m)

abbrev HS (m : ℕ) : Type :=
  ZsS act N localization₂ m ⧸ (Submodule.span (kk P) (Bd act N localization₂ m)).comap (ZsS act N localization₂ m).subtype

def hFib : ℕ → ℕ
  | 0 => Module.finrank (kk P) (Submodule.span (kk P) (Z0 act N localization₂))
  | m + 1 => Module.finrank (kk P) (HS act N localization₂ m)

end Fib

section Numbers

variable (P : LiftProb)

def wtSub {V : Type} (w : Fin P.kind.n → Fin P.kind.n → V) (j : V) : Submodule (kk P) (MM P) where
  carrier := {X | ∀ a b, X a b ≠ 0 → w a b = j}
  add_mem' {X Y} hX hY a b h := by
    by_cases h1 : X a b = 0
    · exact hY a b (by simpa [h1] using h)
    · exact hX a b h1
  zero_mem' a b h := absurd rfl h
  smul_mem' c X hX a b h := hX a b (right_ne_zero_of_mul h)

def gW (j : Wt P.rk) : Submodule (kk P) (MM P) :=
  gLie (kk P) P.kind ⊓ wtSub P (fun a b => P.dg a - P.dg b) j

def locZ : ∀ v (m : ℕ), ((Fin m → P.Gv v) → MM P) → Prop := fun _ _ c => c = 0

def hc (i : ℕ) (j : Wt P.rk) : ℕ :=
  hFib (adAct P.GF P.rbar) (gW P j) (locZ P) i

def h0tw (j : Wt P.rk) : ℕ :=
  Module.finrank (kk P) (invSub (fun g => ((P.cyc g : kk P)) • adAct P.GF P.rbar g) (gW P j))

def h0R (v : P.rPl) (j : Wt P.rk) : ℕ :=
  Module.finrank (kk P) ↥(gW P j ⊓ LinearMap.ker (adAct P.GF P.rbar (P.cv v) - LinearMap.id))

def h0dC (rc : P.Gam → MM P) : ℕ :=
  Module.finrank (kk P) (invSub (fun g => ((P.cyc g : kk P)) • adAct P.GF rc g) (gLie (kk P) P.kind))

end Numbers

class IsCoeff (O : Type) [CommRing O] (l : ℕ) : Prop where
  prime : l.Prime
  odd : l ≠ 2
  dom : IsDomain O
  dvr : IsDiscreteValuationRing O
  complete : IsAdicComplete (maximalIdeal O) O
  char0 : CharZero O
  finRes : Finite (ResidueField O)
  charRes : CharP (ResidueField O) l

def GradedQuotientFiniteness {O : Type} [CommRing O] [IsLocalRing O] {a rk : ℕ} (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)) : Prop :=

  ((m0 wt Jh).IsMaximal ∧ (∀ I : Ideal (A0sub wt Jh), I.IsMaximal → I = m0 wt Jh) ∧
    IsNoetherianRing (A0sub wt Jh) ∧ IsAdicComplete (m0 wt Jh) (A0sub wt Jh)) ∧

  (∃ s : Finset (MvPowerSeries (Fin a) O ⧸ Jh), ((s : Set (MvPowerSeries (Fin a) O ⧸ Jh)) ⊆ (Asub wt Jh : Set _)) ∧
    ∀ x ∈ Asub wt Jh, x ∈ Algebra.adjoin (A0sub wt Jh) (s : Set _)) ∧

  (∀ j, ∃ s : Finset (MvPowerSeries (Fin a) O ⧸ Jh), ((s : Set (MvPowerSeries (Fin a) O ⧸ Jh)) ⊆ (Aj wt Jh j : Set _)) ∧
    ∀ x ∈ Aj wt Jh j, x ∈ Submodule.span (A0sub wt Jh) (s : Set _)) ∧

  Jh = Ideal.span (Jsub wt Jh : Set (MvPowerSeries (Fin a) O)) ∧

  (∀ j, ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧ ∀ M, ∀ x ∈ Aj wt Jh j, x ∈ mhat Jh ^ M →
    x ∈ (m0 wt Jh ^ n M) • Submodule.span (A0sub wt Jh) (Aj wt Jh j : Set _)) ∧

  (∀ f ∈ Psub O wt, f ∈ Jh → f ∈ Jsub wt Jh) ∧

  (IsDomain (MvPowerSeries (Fin a) O ⧸ Jh) → IsDomain (Asub wt Jh)) ∧

  (∃ N : Submodule (A0sub wt Jh) (MvPowerSeries (Fin a) O ⧸ Jh),
    Disjoint (Submodule.span (A0sub wt Jh) (A0sub wt Jh : Set _)) N ∧
    Submodule.span (A0sub wt Jh) (A0sub wt Jh : Set _) ⊔ N =
      Submodule.span (A0sub wt Jh) (Asub wt Jh : Set _)) ∧

  (∀ p : PrimeSpectrum (A0sub wt Jh), ∃ q : PrimeSpectrum (Asub wt Jh),
    q.asIdeal.comap (Subalgebra.inclusion (base_subalgebra_le wt Jh)) = p.asIdeal)

def FiniteTypeRingPart : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) [IsCoeff O l] [IsLocalRing O] (a rk : ℕ) (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)), Jh ≠ ⊤ → IsClosedAdic Jh → IsHomog wt Jh → GradedQuotientFiniteness wt Jh

def PointsLemmaAnyRank : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) [IsCoeff O l] [IsLocalRing O] (a rk : ℕ) (wt : Fin a → Wt rk)
    (Jh : Ideal (MvPowerSeries (Fin a) O)), Jh ≠ ⊤ → IsClosedAdic Jh → IsHomog wt Jh →
  ∀ (kap : Type) [NontriviallyNormedField kap] [IsUltrametricDist kap] [CompleteSpace kap]
    (xi : Asub wt Jh →+* kap),
    (∀ x : A0sub wt Jh, ‖xi (Subalgebra.inclusion (base_subalgebra_le wt Jh) x)‖ ≤ 1) →
    (∀ x ∈ m0 wt Jh, ‖xi (Subalgebra.inclusion (base_subalgebra_le wt Jh) x)‖ < 1) →
  ∃ (kap' : Type) (_ : NontriviallyNormedField kap') (_ : IsUltrametricDist kap')
    (_ : CompleteSpace kap') (_ : NormedAlgebra kap kap') (_ : FiniteDimensional kap kap')
    (t : Fin rk → kap'ˣ),
    (∀ i, ‖tpow t (wt i) * algebraMap kap kap' (xi ⟨mk Jh (X i), mkX_mem_A wt Jh i⟩)‖ < 1) ∧
    ∃ φ : (MvPowerSeries (Fin a) O ⧸ Jh) →+* kap', (∀ y, ‖φ y‖ ≤ 1) ∧
      (∀ y ∈ mhat Jh, ‖φ y‖ < 1) ∧
      ∀ j y (hy : y ∈ Aj wt Jh j), φ y = tpow t j * algebraMap kap kap' (xi ⟨y, Aj_le_A wt Jh hy⟩)

section Prob

variable (P : LiftProb)

def Uq (g : P.Gam) : Prop := ∃ q, g ∈ P.Iq q ∧ g ∈ P.GF ∧ P.rbar g = 1

variable {P}

def EigenA (Q : AQuot P) (j : Wt P.rk) (y : Q.Ahat.C) : Prop :=
  ∀ x, Q.q x = y → MvPowerSeries.map Q.q.toRingHom (P.coBox x) =
    (tpowT P.rk Q.Ahat.C j : TA P.rk Q.Ahat.C) * MvPowerSeries.C y

def IsGrPres {B : Type} [CommRing B] [Algebra P.O B] (eig : Wt P.rk → B → Prop) {a : ℕ}
    (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] B) : Prop :=
  IsClosedAdic Jh ∧ IsHomog wt Jh ∧ ∀ i, eig (wt i) (e (mk Jh (X i)))

variable (P)

def resMap (v : P.lPl) : (P.RV v).C →ₐ[P.O] P.Rbox.C :=
  (P.univV v P.Rbox (fun g => P.uBox g) (by
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := P.uBox_lift
    refine ⟨fun g => h1 g, fun g h => ?_, fun hk g => h3 hk g, fun N g0 => ?_, fun g => h5 g,
      fun _ h => h.elim⟩
    · simp only [Subgroup.coe_mul, Subgroup.mem_comap, Subgroup.coe_subtype, MonoidHom.coe_comp,
        Function.comp_apply]
      exact h2 g h
    · exact (continuous_subtype_val.tendsto g0).eventually (h4 N g0)
  )).exists.choose

def liftZP_unit : Prop :=
  (∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] P.Rbox.C), IsGrPres (IsEigen P.coBox) wt Jh e) ∧
  (∀ v, ∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] (P.RV v).C), IsGrPres (IsEigen (P.coV v)) wt Jh e) ∧
  ∀ Q : AQuot P, ∃ (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e ∧
    (∀ g ∈ P.GF, ∀ i j, Q.q (P.uBox g i j) ∈
      (Aj wt Jh (P.dg i - P.dg j)).map e.toLinearEquiv.toLinearMap) ∧

    (∀ g ∉ P.GF, ∀ i j, Q.q (P.uBox g i j) ∈
      (Aj wt Jh (P.dg i + P.dg j)).map e.toLinearEquiv.toLinearMap) ∧
    maximalIdeal Q.Ahat.C ≤
      Ideal.span {y | ∃ g i j, ∃ c : P.O, y = Q.q (P.uBox g i j) - algebraMap P.O Q.Ahat.C c ∧
        y ∈ maximalIdeal Q.Ahat.C} ⊔ maximalIdeal Q.Ahat.C ^ 2 ⊔
      (maximalIdeal P.O).map (algebraMap P.O Q.Ahat.C)

def UniversalLiftFiniteType : Prop :=
  ∀ (Q : AQuot P) (a : ℕ) (wt : Fin a → Wt P.rk) (Jh : Ideal (MvPowerSeries (Fin a) P.O))
    (e : (MvPowerSeries (Fin a) P.O ⧸ Jh) ≃ₐ[P.O] Q.Ahat.C), IsGrPres (EigenA Q) wt Jh e →
    (∀ g i j, e.symm (Q.q (P.uBox g i j)) ∈ Asub wt Jh) ∧
    ∀ i j (N : ℕ) (g0 : P.Gam), ∀ᶠ g in nhds g0,
      e.symm (Q.q (P.uBox g i j)) - e.symm (Q.q (P.uBox g0 i j)) ∈
        (m0 wt Jh ^ N) • Submodule.span (A0sub wt Jh) (Asub wt Jh : Set _)

def RelPres {S R : Type} [CommRing S] [CommRing R] (ι : S →+* R) (eigS : Wt P.rk → S → Prop)
    (eigR : Wt P.rk → R → Prop) (aw bw : Wt P.rk → ℕ) : Prop :=
  ∃ (a b : ℕ) (wz : Fin a → Wt P.rk) (wf : Fin b → Wt P.rk) (f : Fin b → MvPowerSeries (Fin a) S)
    (e : (MvPowerSeries (Fin a) S ⧸ Ideal.span (Set.range f)) ≃+* R),
    (∀ x, e (Ideal.Quotient.mk _ (MvPowerSeries.C x)) = ι x) ∧
    (∀ i, eigR (wz i) (e (Ideal.Quotient.mk _ (X i)))) ∧
    (∀ k m, eigS (wf k - monoWt wz m) (coeff m (f k))) ∧
    ∀ j, Fintype.card {i // wz i = j} = aw j ∧ Fintype.card {k // wf k = j} = bw j

def RelativePresentation : Prop :=
  RelPres P P.frl.toRingHom (IsEigen P.coRl) (IsEigen P.coFr) (hc P 1) (hc P 2) ∧

  (Fintype.card P.lPl = 1 → ∀ v, RelPres P (resMap P v).toRingHom
    (IsEigen (P.coV v)) (IsEigen P.coBox) (hc P 1) (hc P 2)) ∧
  ∀ j : Wt P.rk, ((j ≠ 0 ∧ h0tw P (-j) = 0) ∨ (j = 0 ∧ h0tw P 0 = 0)) →
    (hc P 1 j : ℤ) - hc P 2 j = -∑ v, (h0R P v j : ℤ)

end Prob

section Lit

variable (P : LiftProb)

def IsRes (rc : P.Gam → MM P) : Prop :=
  (∀ g, IsUnit (rc g).det) ∧
  (∀ g h, rc (g * h) = rc g * (if g ∈ P.GF then rc h else
    residue P.O (P.chi h : P.O) • ((rc h)⁻¹).transpose)) ∧
  (P.kind = .GSp4 → ∀ g, P.kind.Sympl (rc g) (residue P.O (P.chi g : P.O))) ∧
  IsLocallyConstant rc ∧ (∀ g, Uq P g → rc g = 1)

variable {P}

section Grp

variable {H : Type} [Group H] [TopologicalSpace H] (ι : H →* P.Gam) (S : Set P.Gam)
  (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P))

def CochG (m : ℕ) : Submodule (kk P) ((Fin m → H) → MM P) where
  carrier := {c | IsCoch N c ∧ ∀ y z : Fin m → H, (∀ i, (ι (y i))⁻¹ * ι (z i) ∈ S) → c y = c z}
  add_mem' {c c'} hc hc' := ⟨(CochSub m N).add_mem hc.1 hc'.1, fun y z h => by
    simp only [Pi.add_apply]; rw [hc.2 y z h, hc'.2 y z h]⟩
  zero_mem' := ⟨(CochSub m N).zero_mem, fun _ _ _ => rfl⟩
  smul_mem' a c hc := ⟨(CochSub m N).smul_mem a hc.1, fun y z h => by
    simp only [Pi.smul_apply]; rw [hc.2 y z h]⟩

def ZG (m : ℕ) : Submodule (kk P) ((Fin m → H) → MM P) :=
  CochG ι S N m ⊓ LinearMap.ker (dC (fun h : H => act (ι h)) m)

def BG : (m : ℕ) → Submodule (kk P) ((Fin m → H) → MM P)
  | 0 => ⊥
  | m + 1 => (CochG ι S N m).map (dC (fun h : H => act (ι h)) m)

abbrev HG (m : ℕ) : Type := ZG ι S act N m ⧸ (BG ι S act N m).comap (ZG ι S act N m).subtype

def hG (m : ℕ) : ℕ := Module.finrank (kk P) (HG ι S act N m)

def FinCd (d : ℕ) : Prop :=
  (∀ m, FiniteDimensional (kk P) (HG ι S act N m)) ∧ ∀ m, d < m → hG ι S act N m = 0

def chiG : ℤ := (hG ι S act N 0 : ℤ) - hG ι S act N 1 + hG ι S act N 2

def StabG : Prop := ∀ h : H, ∀ X ∈ N, act (ι h) X ∈ N

end Grp

def resAll (m : ℕ) : ((Fin m → P.Gam) → MM P) →ₗ[kk P] FB P m :=
  LinearMap.prod (LinearMap.pi fun q => resL (P.Gq q) m) (LinearMap.pi fun v => resL (P.Gv v) m)

def ZlocS (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) :
    Submodule (kk P) (FB P 2) :=
  Submodule.span (kk P) {y | y ∈ AdmB N 2 ∧ dB act 2 y = 0}

def BlocS (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) :
    Submodule (kk P) (FB P 2) :=
  Submodule.span (kk P) ({y | ∃ a, IsCoch N a ∧ dC act 2 a = 0 ∧ y = resAll 2 a} ∪ dB act 1 '' AdmB N 1)

def cokPT (act : P.Gam → MM P →ₗ[kk P] MM P) (N : Submodule (kk P) (MM P)) : ℕ :=
  Module.finrank (kk P) (ZlocS act N ⧸ (BlocS act N).comap (ZlocS act N).subtype)

variable (P)

def tateFin : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    (StabG (MonoidHom.id P.Gam) (adAct P.GF rc) N →
      FinCd (MonoidHom.id P.Gam) {1} (adAct P.GF rc) N 2) ∧
    (∀ v, StabG (P.Gv v).subtype (adAct P.GF rc) N →
      FinCd (P.Gv v).subtype {1} (adAct P.GF rc) N 2) ∧
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N → FinCd (P.Gq q).subtype {1} (adAct P.GF rc) N 2

def tateGlobal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P), StabG (MonoidHom.id P.Gam) (adAct P.GF rc) N →
    chiG (MonoidHom.id P.Gam) {1} (adAct P.GF rc) N =
      (∑ v, (Module.finrank (kk P) ↥(N ⊓ LinearMap.ker (adAct P.GF rc (P.cv v) - LinearMap.id)) : ℤ)) -
        P.degF * Module.finrank (kk P) N

def tateLocal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    (∀ v, StabG (P.Gv v).subtype (adAct P.GF rc) N →
      chiG (P.Gv v).subtype {1} (adAct P.GF rc) N = -((P.dv v : ℤ) * Module.finrank (kk P) N)) ∧
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N → chiG (P.Gq q).subtype {1} (adAct P.GF rc) N = 0

def unrLocal : Prop :=
  ∀ rc, IsRes P rc → ∀ N : Submodule (kk P) (MM P),
    ∀ q, StabG (P.Gq q).subtype (adAct P.GF rc) N →
      FinCd (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 1 ∧
      hG (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 1 = hG (P.Gq q).subtype (NqSet q) (adAct P.GF rc) N 0

def poitouTate : Prop :=
  (∀ j, cokPT (adAct P.GF P.rbar) (gW P j) = h0tw P (-j)) ∧
  ∀ rc, IsRes P rc → cokPT (adAct P.GF rc) (gLie (kk P) P.kind) = h0dC P rc

def LitG : Prop :=
  tateFin P ∧ tateGlobal P ∧ tateLocal P ∧ unrLocal P ∧ poitouTate P

end Lit

def PointsLemma (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := PointsLemmaAnyRank

end Formalism.MainNotions.UnusedSlot38

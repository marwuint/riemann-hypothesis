import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

section Mod

section Wt

variable {D : D7} {j : ℕ}

theorem wt_ext {w w' : WeightFamilies.Wt D j} (hP : w.aP = w'.aP) (hM : w.aM = w'.aM) (hn : w.n = w'.n) : w = w' := by
  cases w; cases w'; simp only at hP hM hn; subst hP hM hn; rfl

instance wtAdd (D : D7) (j : ℕ) : Add (WeightFamilies.Wt D j) := ⟨wadd⟩

instance wtZero (D : D7) (j : ℕ) : Zero (WeightFamilies.Wt D j) := ⟨wt0 D j⟩

instance wtACM (D : D7) (j : ℕ) : AddCommMonoid (WeightFamilies.Wt D j) where
  add_assoc a b c := wt_ext (by funext τ i; exact Nat.add_assoc _ _ _) (by funext τ i; exact Nat.add_assoc _ _ _)
    (Nat.add_assoc _ _ _)
  zero_add a := wt_ext (by funext τ i; exact Nat.zero_add _) (by funext τ i; exact Nat.zero_add _) (Nat.zero_add _)
  add_zero a := wt_ext (by funext τ i; exact Nat.add_zero _) (by funext τ i; exact Nat.add_zero _) (Nat.add_zero _)
  add_comm a b := wt_ext (by funext τ i; exact Nat.add_comm _ _) (by funext τ i; exact Nat.add_comm _ _) (Nat.add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

theorem wt_add_def (w w' : WeightFamilies.Wt D j) : w + w' = wadd w w' := rfl

end Wt

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mulS (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd la (x * y) = vAdd la x + vAdd la y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem vAdd_nonneg_iffS (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 ≤ vAdd la x ↔ la.valuation K x ≤ 1 := by
  unfold vAdd
  by_cases h0 : la.valuation K x = 0
  · rw [h0]; simp
  · rw [neg_nonneg, ← WithZero.log_le_log h0 one_ne_zero]; simp

theorem vAdd_addS (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vAdd la x) (vAdd la y) ≤ vAdd la (x + y) := by
  unfold vAdd
  have h := Valuation.map_add (la.valuation K) x y
  have hx' : la.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  have hy' : la.valuation K y ≠ 0 := (map_ne_zero _).2 hy
  have hxy' : la.valuation K (x + y) ≠ 0 := (map_ne_zero _).2 hxy
  rcases le_total (la.valuation K x) (la.valuation K y) with hle | hle
  · rw [max_eq_right hle] at h
    have := (WithZero.log_le_log hxy' hy').2 h
    exact min_le_of_right_le (by linarith)
  · rw [max_eq_left hle] at h
    have := (WithZero.log_le_log hxy' hx').2 h
    exact min_le_of_left_le (by linarith)

def vE (la : HeightOneSpectrum (𝓞 K)) (x : K) : EReal :=
  open Classical in if x = 0 then ⊤ else (((vAdd la x : ℤ) : ℝ) : EReal)

theorem vE_zero (la : HeightOneSpectrum (𝓞 K)) : vE la (0 : K) = ⊤ := by simp [vE]

theorem vE_of_ne (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    vE la x = (((vAdd la x : ℤ) : ℝ) : EReal) := by simp [vE, hx]

theorem vE_ne_bot (la : HeightOneSpectrum (𝓞 K)) (x : K) : vE la x ≠ ⊥ := by
  unfold vE; split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

theorem vE_mul (la : HeightOneSpectrum (𝓞 K)) (x y : K) : vE la (x * y) = vE la x + vE la y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, vE_zero, EReal.top_add_of_ne_bot (vE_ne_bot la y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, vE_zero, EReal.add_top_of_ne_bot (vE_ne_bot la x)]
  rw [vE_of_ne la (mul_ne_zero hx hy), vE_of_ne la hx, vE_of_ne la hy, vAdd_mulS la hx hy]
  push_cast; rfl

theorem vE_add (la : HeightOneSpectrum (𝓞 K)) (x y : K) : min (vE la x) (vE la y) ≤ vE la (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, vE_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; rw [zero_add]; exact min_le_right _ _
  by_cases hy : y = 0
  · subst hy; rw [add_zero]; exact min_le_left _ _
  rw [vE_of_ne la hx, vE_of_ne la hy, vE_of_ne la hxy]
  rcases min_le_iff.1 (vAdd_addS la hx hy hxy) with h | h
  · exact min_le_of_left_le (by exact_mod_cast h)
  · exact min_le_of_right_le (by exact_mod_cast h)

theorem vE_nonneg_iff (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    0 ≤ vE la x ↔ la.valuation K x ≤ 1 := by
  rw [vE_of_ne la hx, ← vAdd_nonneg_iffS]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

end Val

section Model

variable (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O)
  (Sg : ∀ j, WeightFamilies.Wt D j → Prop)

def cuspS (p : Prop) : Submodule K K := open Classical in if p then ⊤ else ⊥

def mlatS (p : Prop) : Submodule (𝓞 K) ↥(cuspS K p) :=
  (LinearMap.range (Algebra.linearMap (𝓞 K) K)).comap ((cuspS K p).subtype.restrictScalars (𝓞 K))

theorem mem_mlatS {p : Prop} (F : ↥(cuspS K p)) : F ∈ mlatS K p ↔ ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (F : K) := by
  simp [mlatS]

abbrev provS : WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun j w => ↥(cuspS K (Sg j w))
  Mlat := fun j w => mlatS K (Sg j w)
  supN := fun _ _ σ F => ‖σ (F : K)‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  supN_smul := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ (F : K)‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  l2Norm_smul_alt := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0

variable {D K Sg}

def oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : (provS D K e Sg).Cusp j w :=
  ⟨1, by simp [cuspS, h]⟩

theorem coe_oneS {j : ℕ} {w : WeightFamilies.Wt D j} (h : Sg j w) : ((oneS e h : (provS D K e Sg).Cusp j w) : K) = 1 := rfl

variable (K) in

def sWS {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 K := ((qq D ^ DF w : ℕ) : 𝓞 K)

def evS (j : ℕ) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₐ[K] K := AddMonoidAlgebra.lift K K (WeightFamilies.Wt D j) 1

theorem evS_single (j : ℕ) (w : WeightFamilies.Wt D j) (a : K) : evS (D := D) (K := K) j (AddMonoidAlgebra.single w a) = a := by
  rw [evS, AddMonoidAlgebra.lift_single]; simp

def incS (j : ℕ) (w : WeightFamilies.Wt D j) : (provS D K e Sg).Cusp j w →ₗ[K] AddMonoidAlgebra K (WeightFamilies.Wt D j) where
  toFun F := AddMonoidAlgebra.single w (F : K)
  map_add' F G := by rw [Submodule.coe_add, AddMonoidAlgebra.single_add]
  map_smul' c F := by rw [Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, AddMonoidAlgebra.smul_single']

theorem incS_apply (j : ℕ) (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    incS e j w F = AddMonoidAlgebra.single w (F : K) := rfl

theorem evS_incS (j : ℕ) (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    evS (D := D) (K := K) j (incS e j w F) = (F : K) := evS_single j w _

def coefS (j : ℕ) (w : WeightFamilies.Wt D j) : AddMonoidAlgebra K (WeightFamilies.Wt D j) →ₗ[K] K where
  toFun F := F.coeff w
  map_add' F G := by rw [AddMonoidAlgebra.coeff_add]; rfl
  map_smul' c F := by rw [AddMonoidAlgebra.coeff_smul]; rfl

open Classical in
theorem coefS_single (j : ℕ) (w w' : WeightFamilies.Wt D j) (a : K) :
    coefS (D := D) (K := K) j w (AddMonoidAlgebra.single w' a) = if w' = w then a else 0 := by
  classical
  show (AddMonoidAlgebra.single w' a).coeff w = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

variable (Sg)

def pjS (hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w')) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (dat : P.Dat)
    (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1)
    (hPt : ∀ p, Nonempty ((P.loc dat p).Pt (P.loc dat p).YY)) : PJ D (provS D K e Sg) P j where
  Forms := AddMonoidAlgebra K (WeightFamilies.Wt D j)
  rF := inferInstance
  aF := (inferInstance : Algebra K (AddMonoidAlgebra K (WeightFamilies.Wt D j)))
  aFO := (inferInstance : Algebra (𝓞 K) (AddMonoidAlgebra K (WeightFamilies.Wt D j)))
  stF := IsScalarTower.of_algebraMap_eq fun x => rfl
  inc := fun w => incS e j w
  inc_inj := fun w F G h => Subtype.ext (by
    have := congrArg (evS (D := D) (K := K) j) h
    rwa [evS_incS, evS_incS] at this)
  inc_indep := by
    classical
    rw [iSupIndep_def]
    intro w
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨F, rfl⟩ := LinearMap.mem_range.1 hx
    have hle : (⨆ w' ≠ w, LinearMap.range (incS (Sg := Sg) e j w')) ≤ LinearMap.ker (coefS (D := D) (K := K) j w) := by
      refine iSup₂_le fun w' hw' => ?_
      rintro _ ⟨G, rfl⟩
      rw [LinearMap.mem_ker, incS_apply, coefS_single, if_neg hw']
    have h0 := hle hx'
    rw [LinearMap.mem_ker, incS_apply, coefS_single, if_pos rfl] at h0
    rw [incS_apply, h0, AddMonoidAlgebra.single_zero]
  inc_mul := fun w w' F G => by
    refine ⟨⟨(F : K) * (G : K), ?_⟩, ?_⟩
    · by_cases hF : Sg j w
      · by_cases hG : Sg j w'
        · simp [cuspS, hadd j w w' hF hG]
        · have := G.2; simp only [cuspS, hG, if_false, Submodule.mem_bot] at this
          rw [this, mul_zero]; exact Submodule.zero_mem _
      · have := F.2; simp only [cuspS, hF, if_false, Submodule.mem_bot] at this
        rw [this, zero_mul]; exact Submodule.zero_mem _
    · show AddMonoidAlgebra.single w (F : K) * AddMonoidAlgebra.single w' (G : K) =
        AddMonoidAlgebra.single (wadd w w') ((F : K) * (G : K))
      rw [AddMonoidAlgebra.single_mul_single]; rfl
  dat := dat
  dat_rk := h1
  dat_jj := h2
  Pt := fun la => (P.loc dat (resCh la)).Pt (P.loc dat (resCh la)).YY
  pt66 := fun _ y => y
  vAt := fun la _ F => vE la (evS (D := D) (K := K) j F)
  vAt_zero := fun la _ => by rw [map_zero, vE_zero]
  vAt_ne_bot := fun la _ F => vE_ne_bot la _
  vAt_add := fun la _ F G => by rw [map_add]; exact vE_add la _ _
  vAt_smul := fun la _ a F ha => by
    rw [map_smul, smul_eq_mul, vE_mul, vE_of_ne la ha]
  vAt_mul := fun la _ w w' F G => by rw [map_mul, vE_mul]
  Mlat_eq := fun w F => by
    rw [show F ∈ (provS D K e Sg).Mlat j w ↔ _ from mem_mlatS K F]
    constructor
    · rintro ⟨r, hr⟩ la y
      show 0 ≤ vE la (evS (D := D) (K := K) j (incS e j w F))
      rw [evS_incS]
      by_cases h0 : (F : K) = 0
      · rw [h0, vE_zero]; exact le_top
      · rw [vE_nonneg_iff la h0, ← hr]; exact la.valuation_le_one r
    · intro h
      by_cases h0 : (F : K) = 0
      · exact ⟨0, by rw [map_zero, h0]⟩
      · have hv : ∀ la : HeightOneSpectrum (𝓞 K), la.valuation K (F : K) ≤ 1 := fun la => by
          obtain ⟨y⟩ := hPt (resCh la)
          have := h la y
          change 0 ≤ vE la (evS (D := D) (K := K) j (incS e j w F)) at this
          rw [evS_incS] at this
          exact (vE_nonneg_iff la h0).1 this
        obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (F : K) hv
        exact ⟨r, hr⟩
  thAll := fun w => ((provS D K e Sg).Mlat j w).comap (sWS K w • LinearMap.id)
  shortTh := fun w => (provS D K e Sg).Mlat j w

end Model

section Lemmas

variable {D : D7} {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) {Sg : ∀ j, WeightFamilies.Wt D j → Prop}
  (hadd : ∀ j w w', Sg j w → Sg j w' → Sg j (wadd w w')) (P : ModuliIntegralCharts.Prov D) {j : ℕ} (dat : P.Dat)
  (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1)
  (hPt : ∀ p, Nonempty ((P.loc dat p).Pt (P.loc dat p).YY))

theorem pjS_inc (w : WeightFamilies.Wt D j) (F : (provS D K e Sg).Cusp j w) :
    (pjS e Sg hadd P j dat h1 h2 hPt).inc w F = AddMonoidAlgebra.single w (F : K) := rfl

theorem pjS_vAt (la : HeightOneSpectrum (𝓞 K)) (y : (pjS e Sg hadd P j dat h1 h2 hPt).Pt la)
    (F : (pjS e Sg hadd P j dat h1 h2 hPt).Forms) :
    (pjS e Sg hadd P j dat h1 h2 hPt).vAt la y F = vE la (evS (D := D) (K := K) j F) := rfl

end Lemmas

end Mod

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Inh

end

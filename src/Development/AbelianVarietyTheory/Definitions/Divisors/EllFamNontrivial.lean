import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

open CategoryTheory GlobalTheory.CatCoh

abbrev Tot (I : Type) (g : ℕ) : Type := (I → ℂ) × (Fin g → ℂ)

structure Fam (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] where

  V : Opens (I → ℂ)

  τ : Λ →+ ((I → ℂ) → Fin g → ℂ)
  hol : ∀ l, AnalyticOnNhd ℂ (τ l) V

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]

def Fam.shift (F : Fam I g Λ) (l : Λ) (p : Tot I g) : Tot I g := (p.1, p.2 + F.τ l p.1)

theorem Fam.shift_zero (F : Fam I g Λ) (p : Tot I g) : F.shift 0 p = p := by
  simp [Fam.shift]

theorem Fam.shift_add (F : Fam I g Λ) (l m : Λ) (p : Tot I g) : F.shift (l + m) p = F.shift l (F.shift m p) := by
  simp only [Fam.shift, map_add, Pi.add_apply, Prod.mk.injEq, true_and]
  abel

theorem Fam.shift_analytic (F : Fam I g Λ) (l : Λ) {W : Set (Tot I g)} (h : ∀ p ∈ W, p.1 ∈ F.V) :
    AnalyticOnNhd ℂ (F.shift l) W := by
  intro p hp
  exact analyticAt_fst.prod (analyticAt_snd.add ((F.hol l p.1 (h p hp)).comp analyticAt_fst))

def dw {W : Opens (Tot I g)} (a : Fin g) : Derivation ℂ (Hol W) (Hol W) := Hol.der ((0, Pi.single a 1) : Tot I g)

def Step {W : Opens (Tot I g)} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W →+* C) : Prop :=
  ∃ n : Fin g → C, (∀ a, n a ∈ J) ∧ (∀ a b, n a * n b = 0) ∧ ∀ h, ρ₂ h = ρ₁ h + ∑ a, ρ₁ (dw a h) * n a

def Close {W : Opens (Tot I g)} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W →+* C) : Prop :=
  Relation.ReflTransGen (Step J) ρ₁ ρ₂

theorem Close.map {W : Opens (Tot I g)} {C C' : Type} [CommRing C] [CommRing C'] {J : Ideal C} {J' : Ideal C'}
    {ρ₁ ρ₂ : Hol W →+* C} (h : Close J ρ₁ ρ₂) (φ : C →+* C') (hφ : ∀ c ∈ J, φ c ∈ J') :
    Close J' (φ.comp ρ₁) (φ.comp ρ₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨n, hn, hnn, hρ⟩ := hs
    refine ih.tail ⟨fun a ↦ φ (n a), fun a ↦ hφ _ (hn a), fun a b ↦ by rw [← map_mul, hnn, map_zero], fun f ↦ ?_⟩
    simp only [RingHom.comp_apply, hρ, map_add, map_sum, map_mul]

theorem Close.comap {W W' : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W' →+* C} (h : Close J ρ₁ ρ₂) (ψ : Hol W →+* Hol W') (hψ : ∀ a f, dw a (ψ f) = ψ (dw a f)) :
    Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨n, hn, hnn, hρ⟩ := hs
    exact ih.tail ⟨n, hn, hnn, fun f ↦ by simp only [RingHom.comp_apply, hρ, hψ]⟩

theorem Close.sub_mem {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {ρ₁ ρ₂ : Hol W →+* C}
    (h : Close J ρ₁ ρ₂) (f : Hol W) : ρ₂ f - ρ₁ f ∈ J := by
  induction h with
  | refl => simp
  | @tail b c _ hs ih =>
    obtain ⟨n, hn, -, hρ⟩ := hs
    have e : c f - ρ₁ f = (b f - ρ₁ f) + ∑ a, b (dw a f) * n a := by
      rw [hρ]
      ring
    rw [e]
    exact J.add_mem ih (J.sum_mem fun a _ ↦ J.mul_mem_left _ (hn a))

structure Charts (F : Fam I g Λ) : Type 1 where

  K : Type

  W : K → Opens (Tot I g)
  base : ∀ k, ∀ p ∈ W k, p.1 ∈ F.V

  le : Λ → K → K → Prop
  le_refl : ∀ k, le 0 k k
  le_trans : ∀ {l m k k' k''}, le l k' k → le m k'' k' → le (l + m) k'' k
  maps : ∀ {l k k'}, le l k' k → ∀ p ∈ W k', F.shift l p ∈ W k

def Fam.tot (F : Fam I g Λ) : Opens (Tot I g) := ⟨Prod.fst ⁻¹' F.V, F.V.isOpen.preimage continuous_fst⟩

def Fam.allCharts (F : Fam I g Λ) : Charts F where
  K := {W : Opens (Tot I g) // ∀ p ∈ W, p.1 ∈ F.V}
  W k := k.1
  base k := k.2
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

def Fam.totChart (F : Fam I g Λ) : F.allCharts.K := ⟨F.tot, fun _ h ↦ h⟩

namespace Charts

variable {F : Fam I g Λ} (K : Charts F)

def Rich : Prop :=
  (∀ p : Tot I g, p.1 ∈ F.V → ∃ k, p ∈ K.W k) ∧
    ∀ l k₁ k₂ p, p ∈ K.W k₁ → F.shift l p ∈ K.W k₂ → ∃ k, p ∈ K.W k ∧ K.le 0 k k₁ ∧ K.le l k k₂

def Based : Prop := ∃ k, ∀ z ∈ F.V, ((z, 0) : Tot I g) ∈ K.W k

def cst (k : K.K) : Hol F.V →+* Hol (K.W k) :=
  (Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K.base k)).toRingHom

variable {K} in

def sh {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →+* Hol (K.W k') :=
  (Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)).toRingHom

theorem fn_cst (k : K.K) (f : Hol F.V) {p : Tot I g} (hp : p ∈ K.W k) : (K.cst k f).fn p = f.fn p.1 := by
  exact Hol.fn_comap _ _ _ f hp

variable {K}

theorem fn_sh {l : Λ} {k k' : K.K} (h : K.le l k' k) (f : Hol (K.W k)) {p : Tot I g} (hp : p ∈ K.W k') :
    (sh h f).fn p = f.fn (F.shift l p) := by
  exact Hol.fn_comap _ _ _ f hp

theorem sh_refl {k : K.K} (h : K.le 0 k k) (f : Hol (K.W k)) : sh h f = f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h f hp, F.shift_zero]

theorem sh_sh {l m : Λ} {k k' k'' : K.K} (h : K.le l k' k) (h' : K.le m k'' k') (h'' : K.le (l + m) k'' k)
    (f : Hol (K.W k)) : sh h' (sh h f) = sh h'' f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h' _ hp, fn_sh h f (K.maps h' p hp), fn_sh h'' f hp, F.shift_add]

theorem sh_cst {l : Λ} {k k' : K.K} (h : K.le l k' k) (f : Hol F.V) : sh h (K.cst k f) = K.cst k' f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h _ hp, K.fn_cst k f (K.maps h p hp), K.fn_cst k' f hp]
  rfl

theorem dw_sh {l : Λ} {k k' : K.K} (h : K.le l k' k) (a : Fin g) (f : Hol (K.W k)) : dw a (sh h f) = sh h (dw a f) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hb : p.1 ∈ F.V := K.base k' p hp
  have hD : HasFDerivAt (F.τ l) (fderiv ℂ (F.τ l) p.1) p.1 :=
    (F.hol l p.1 hb).differentiableAt.hasFDerivAt
  have hΦ : HasFDerivAt (F.shift l) ((ContinuousLinearMap.fst ℂ (I → ℂ) (Fin g → ℂ)).prod
      (ContinuousLinearMap.snd ℂ (I → ℂ) (Fin g → ℂ) +
        (fderiv ℂ (F.τ l) p.1).comp (ContinuousLinearMap.fst ℂ (I → ℂ) (Fin g → ℂ)))) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add (hD.comp p hasFDerivAt_fst))
  have hder : fderiv ℂ (F.shift l) p ((0, Pi.single a 1) : Tot I g) = (0, Pi.single a 1) := by
    rw [hΦ.fderiv]
    simp
  have e1 := Hol.fn_der_comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)
    ((0, Pi.single a 1) : Tot I g) f hp
  have e2 := Hol.fn_comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)
    (Hol.der ((0, Pi.single a 1) : Tot I g) f) hp
  have e3 := Hol.fn_der ((0, Pi.single a 1) : Tot I g) f (K.maps h p hp)
  rw [hder] at e1
  exact e1.trans (e2.trans e3).symm

theorem dw_cst (k : K.K) (a : Fin g) (f : Hol F.V) : dw a (K.cst k f) = 0 := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have e1 := Hol.fn_der_comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K.base k)
    ((0, Pi.single a 1) : Tot I g) f hp
  rw [fderiv_fst] at e1
  simp only [ContinuousLinearMap.coe_fst', map_zero] at e1
  rw [Hol.fn_of_mem (0 : Hol (K.W k)) hp]
  exact e1.trans rfl

variable (K) in

structure Obj : Type 1 where

  k : K.K

  C : Type
  [ring : CommRing C]
  [alg : Algebra (Hol F.V) C]

  J : Ideal C
  nil : IsNilpotent J

  ρ : Hol (K.W k) →+* C
  ρ_cst : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) C f

attribute [instance] Obj.ring Obj.alg

structure Hom (T T' : K.Obj) where

  φ : T.C →ₐ[Hol F.V] T'.C

  deg : Λ
  le : K.le deg T'.k T.k
  mem : ∀ c ∈ T.J, φ c ∈ T'.J
  close : Close T'.J (T'.ρ.comp (sh le)) ((φ : T.C →+* T'.C).comp T.ρ)

theorem Hom.ext' {T T' : K.Obj} {f f' : Hom T T'} (h : ∀ c, f.φ c = f'.φ c) (h' : f.deg = f'.deg) : f = f' := by
  obtain ⟨φ, d, le, mem, cl⟩ := f
  obtain ⟨φ', d', le', mem', cl'⟩ := f'
  obtain rfl : φ = φ' := AlgHom.ext h
  obtain rfl : d = d' := h'
  rfl

instance : Category K.Obj where
  Hom := Hom
  id T := ⟨AlgHom.id _ _, 0, K.le_refl _, fun _ h ↦ h, by
    rw [show T.ρ.comp (sh (K.le_refl T.k)) = T.ρ from RingHom.ext fun f ↦ congrArg T.ρ (sh_refl _ f)]
    exact Relation.ReflTransGen.refl⟩
  comp {T T' T''} f f' := ⟨f'.φ.comp f.φ, f.deg + f'.deg, K.le_trans f.le f'.le, fun c h ↦ f'.mem _ (f.mem c h), by
    rw [show T''.ρ.comp (sh (K.le_trans f.le f'.le)) = (T''.ρ.comp (sh f'.le)).comp (sh f.le) from
      RingHom.ext fun h ↦ congrArg T''.ρ (sh_sh f.le f'.le _ h).symm]
    exact Relation.ReflTransGen.trans (f'.close.comap (sh f.le) (dw_sh f.le)) (f.close.map (f'.φ : T'.C →+* T''.C) f'.mem)⟩
  id_comp f := Hom.ext' (fun _ ↦ rfl) (zero_add _)
  comp_id f := Hom.ext' (fun _ ↦ rfl) (add_zero _)
  assoc f f' f'' := Hom.ext' (fun _ ↦ rfl) (add_assoc _ _ _)

theorem hom_ext {T T' : K.Obj} {f f' : T ⟶ T'} (h : ∀ c, f.φ c = f'.φ c) (h' : f.deg = f'.deg) : f = f' := by
  obtain ⟨φ, d, le, mem, cl⟩ := f
  obtain ⟨φ', d', le', mem', cl'⟩ := f'
  obtain rfl : φ = φ' := AlgHom.ext h
  obtain rfl : d = d' := h'
  rfl

@[simp] theorem comp_φ {T T' T'' : K.Obj} (f : T ⟶ T') (f' : T' ⟶ T'') (c : T.C) : (f ≫ f').φ c = f'.φ (f.φ c) := rfl

@[simp] theorem comp_deg {T T' T'' : K.Obj} (f : T ⟶ T') (f' : T' ⟶ T'') : (f ≫ f').deg = f.deg + f'.deg := rfl

@[simp] theorem id_deg (T : K.Obj) : Hom.deg (𝟙 T) = 0 := rfl

variable (K) in

@[reducible] def Oc : K.Obj ⥤ CommAlgCat.{0} (Hol F.V) where
  obj T := CommAlgCat.of _ T.C
  map f := CommAlgCat.ofHom f.φ

theorem mp_Oc {T T' : K.Obj} (f : T ⟶ T') : mp K.Oc f = f.φ := rfl

variable (K) in

def perZ (per : Λ →+ Hol F.V) : Z1 K.Oc :=
  ⟨fun _ T' f ↦ algebraMap (Hol F.V) T'.C (per f.deg), fun T T' T'' f f' ↦ by
    change algebraMap _ T''.C (per (f.deg + f'.deg)) = f'.φ (algebraMap _ _ _) + algebraMap _ T''.C _
    rw [AlgHom.commutes, map_add, map_add]⟩

variable (K) in

def perCl (per : Λ →+ Hol F.V) : H1 K.Oc := H1.mk _ (K.perZ per)

variable (K) in

@[reducible] def triv (k : K.K) : K.Obj where
  k := k
  C := Hol (K.W k)
  alg := (K.cst k).toAlgebra
  J := ⊥
  nil := ⟨1, by simp⟩
  ρ := RingHom.id _
  ρ_cst _ := rfl

def fromTriv {l : Λ} {k : K.K} (T : K.Obj) (h : K.le l T.k k) (ρ : Hol (K.W k) →+* T.C)
    (hc : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) T.C f) (hρ : Close T.J (T.ρ.comp (sh h)) ρ) : K.triv k ⟶ T where
  φ := letI := (K.triv k).alg; { ρ with commutes' := hc }
  deg := l
  le := h
  mem c hc := by rw [Ideal.mem_bot.1 hc, map_zero]; exact T.J.zero_mem
  close := hρ

def ptHom {l : Λ} {k : K.K} (T : K.Obj) (h : K.le l T.k k) : K.triv k ⟶ T :=
  fromTriv T h (T.ρ.comp (sh h)) (fun f ↦ (congrArg T.ρ (sh_cst h f)).trans (T.ρ_cst f)) Relation.ReflTransGen.refl

end Charts

def Fam.transl (F : Fam I g Λ) (l : Λ) : F.allCharts.triv F.totChart ⟶ F.allCharts.triv F.totChart :=
  Charts.ptHom (l := l) (F.allCharts.triv F.totChart) (fun _ h ↦ h)

theorem Fam.transl_deg (F : Fam I g Λ) (l : Λ) : (F.transl l).deg = l := rfl

def Charts.dualAt {F : Fam I g Λ} (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) : K.Obj where
  k := k
  C := DualNumber ℂ
  alg := (((algebraMap ℂ (DualNumber ℂ)).comp (Hol.ev p hp).toRingHom).comp (K.cst k)).toAlgebra
  J := Ideal.span {DualNumber.eps}
  nil := ⟨2, by rw [Ideal.span_singleton_pow, sq, DualNumber.eps_mul_eps]; simp⟩
  ρ := (algebraMap ℂ (DualNumber ℂ)).comp (Hol.ev p hp).toRingHom
  ρ_cst _ := rfl

theorem Charts.dualAt_J_ne_bot {F : Fam I g Λ} (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) :
    (K.dualAt k p hp).J ≠ ⊥ := by
  change Ideal.span {DualNumber.eps} ≠ ⊥
  rw [Ne, Ideal.span_singleton_eq_bot]
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

end GlobalTheory.AnPer

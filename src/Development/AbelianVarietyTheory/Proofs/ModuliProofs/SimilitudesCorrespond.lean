import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
open scoped TensorProduct

namespace GlobalTheory.LevelCompare

theorem zhat_ext {z w : Zhat} (h : ∀ n, Zhat.red n z = Zhat.red n w) : z = w :=
  Subtype.ext (funext h)

theorem red_compat (z : Zhat) (m n : ℕ+) (h : (m : ℕ) ∣ n) : ZMod.castHom h (ZMod m) (Zhat.red n z) = Zhat.red m z :=
  z.2 m n h

theorem exists_zhat (c : ℕ+ → ℤ) (hc : ∀ m n : ℕ+, (m : ℕ) ∣ n → ((m : ℕ) : ℤ) ∣ c n - c m) :
    ∃ z : Zhat, ∀ n, Zhat.red n z = c n :=
  ⟨⟨fun n => c n, fun m n h => by
    rw [map_intCast]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (hc m n h) |>.symm⟩, fun _ => rfl⟩

theorem exists_eq_mul {n : ℕ+} {z : Zhat} (h : Zhat.red n z = 0) : ∃ w : Zhat, z = (n : ℕ) * w := by
  have key : ∀ m : ℕ+, ∃ c : ℤ, Zhat.red (n * m) z = ((n : ℕ) * c : ℤ) := fun m => by
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Zhat.red (n * m) z)
    have h1 := red_compat z n (n * m) (by simp)
    rw [← hk, map_intCast, h, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    obtain ⟨c, rfl⟩ := h1
    exact ⟨c, hk.symm⟩
  choose c hc using key
  obtain ⟨w, hw⟩ := exists_zhat c fun m m' h => by
    have h1 := red_compat z (n * m) (n * m') (by simpa using Nat.mul_dvd_mul_left n h)
    rw [hc, hc, map_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← mul_sub] at h1
    push_cast at h1
    have := (mul_dvd_mul_iff_left (a := ((n : ℕ) : ℤ)) (by simp)).1 h1
    rwa [dvd_sub_comm] at this
  refine ⟨w, zhat_ext fun m => ?_⟩
  rw [← red_compat z m (n * m) (by simp), hc, map_intCast, map_mul, hw, map_natCast]
  push_cast
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem exists_basis (D : Datum H) : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ D.La) := by
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  exact ⟨_, ⟨Module.finBasis ℤ D.La⟩⟩

def mulSub (D : Datum H) (n : ℕ) : Submodule Zhat (Lhat D) := LinearMap.range (LinearMap.lsmul Zhat (Lhat D) n)

theorem mem_mulSub {n : ℕ} {x : Lhat D} : x ∈ mulSub D n ↔ ∃ y, x = (n : Zhat) • y :=
  ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩

theorem map_mem_mulSub {n : ℕ} {x : Lhat D} (g : Lhat D →ₗ[Zhat] Lhat D) (h : x ∈ mulSub D n) : g x ∈ mulSub D n := by
  obtain ⟨y, rfl⟩ := mem_mulSub.1 h
  exact mem_mulSub.2 ⟨g y, map_smul _ _ _⟩

theorem tmul_nsmul (n : ℕ) (a : D.La) : (1 : Zhat) ⊗ₜ[ℤ] (n • a) = (n : Zhat) • (1 : Zhat) ⊗ₜ[ℤ] a := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (TensorProduct.mk ℤ Zhat D.La 1) n a

theorem tmul_mem_mulSub {n : ℕ} {a : D.La} (h : D.ModN n a) : (1 : Zhat) ⊗ₜ[ℤ] a ∈ mulSub D n := by
  obtain ⟨b, rfl⟩ := h
  exact mem_mulSub.2 ⟨1 ⊗ₜ b, tmul_nsmul n b⟩

theorem mem_of_tmul {N : Type} [AddCommGroup N] [Module Zhat N] (P : Submodule Zhat N) (φ : Lhat D →ₗ[Zhat] N)
    (h : ∀ a, φ (1 ⊗ₜ a) ∈ P) (x : Lhat D) : φ x ∈ P := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a =>
    have : z ⊗ₜ[ℤ] a = z • ((1 : Zhat) ⊗ₜ[ℤ] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact P.smul_mem _ (h a)
  | add x y hx hy => rw [map_add]; exact P.add_mem hx hy

theorem mulSub_le {n : ℕ} {𝔞 : Ideal (𝓞 E)} (h : (n : 𝓞 E) ∈ 𝔞) : mulSub D n ≤ hatSub D 𝔞 := by
  rintro _ ⟨y, rfl⟩
  refine mem_of_tmul (hatSub D 𝔞) (LinearMap.lsmul Zhat (Lhat D) n) (fun a => ?_) y
  refine Submodule.subset_span ⟨(n : 𝓞 E) • a, Submodule.smul_mem_smul h trivial, ?_⟩
  simp only [LinearMap.lsmul_apply]
  rw [Nat.cast_smul_eq_nsmul, tmul_nsmul]

theorem modN_iff {n : ℕ} {a : D.La} :
    D.ModN n a ↔ a ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Nat.cast_smul_eq_nsmul, Submodule.mem_top, true_and, Datum.ModN, eq_comm]

theorem hatSub_span (n : ℕ) : hatSub D (Ideal.span {(n : 𝓞 E)}) = mulSub D n := by
  refine le_antisymm (Submodule.span_le.2 ?_) (mulSub_le (Ideal.mem_span_singleton_self _))
  rintro _ ⟨a, ha, rfl⟩
  exact tmul_mem_mulSub (modN_iff.2 ha)

theorem exists_approx {n : ℕ} (hn : 0 < n) (x : Lhat D) : ∃ a : D.La, x - 1 ⊗ₜ a ∈ mulSub D n := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul z a =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Zhat.red ⟨n, hn⟩ z)
    obtain ⟨w, hw⟩ := exists_eq_mul (n := ⟨n, hn⟩) (z := z - k) (by rw [map_sub, map_intCast, hk, sub_self])
    refine ⟨k • a, mem_mulSub.2 ⟨w ⊗ₜ a, ?_⟩⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← TensorProduct.smul_tmul, ← TensorProduct.sub_tmul, zsmul_one, hw]
    rfl
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert Submodule.add_mem _ ha hb using 1
    rw [TensorProduct.tmul_add]; abel

theorem tmul_mem_hatSub {n : ℕ} (hn : 0 < n) {𝔞 : Ideal (𝓞 E)} (h : (n : 𝓞 E) ∈ 𝔞) {a : D.La} :
    (1 : Zhat) ⊗ₜ[ℤ] a ∈ hatSub D 𝔞 ↔ a ∈ 𝔞 • (⊤ : Submodule (𝓞 E) D.La) := by
  refine ⟨fun ha => ?_, fun ha => Submodule.subset_span ⟨a, ha, rfl⟩⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  let Q := D.La ⧸ 𝔞 • (⊤ : Submodule (𝓞 E) D.La)
  have hQ : ∀ x : Q, n • x = 0 := fun x => by
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul h trivial
  letI : Module (ZMod n) Q := AddCommMonoid.zmodModule hQ
  letI : Module Zhat Q := Module.compHom Q (show Zhat →+* ZMod n from Zhat.red ⟨n, hn⟩)
  let q : Lhat D →ₗ[Zhat] Q :=
    LinearMap.liftBaseChange Zhat ((𝔞 • (⊤ : Submodule (𝓞 E) D.La)).mkQ.toAddMonoidHom.toIntLinearMap)
  have hq : ∀ b : D.La, q (1 ⊗ₜ b) = Submodule.Quotient.mk b := fun b => by simp [q]
  have : hatSub D 𝔞 ≤ LinearMap.ker q := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact (hq b).trans ((Submodule.Quotient.mk_eq_zero _).2 hb))
  exact (Submodule.Quotient.mk_eq_zero _).1 ((hq a).symm.trans (this ha))

theorem tmul_mem_mulSub_iff {n : ℕ} (hn : 0 < n) {a : D.La} : (1 : Zhat) ⊗ₜ[ℤ] a ∈ mulSub D n ↔ D.ModN n a := by
  rw [← hatSub_span, tmul_mem_hatSub hn (Ideal.mem_span_singleton_self _), modN_iff]

theorem eq_zero_of_mem {x : Lhat D} (h : ∀ n, 0 < n → x ∈ mulSub D n) : x = 0 := by
  obtain ⟨k, ⟨b⟩⟩ := exists_basis D
  refine (b.baseChange Zhat).ext_elem fun i => zhat_ext fun n => ?_
  obtain ⟨y, rfl⟩ := mem_mulSub.1 (h n n.2)
  simp

theorem exists_limit (a : ℕ → D.La) (ha : ∀ n m, 0 < n → 0 < m → D.ModN n (a (n * m) - a n)) :
    ∃ x : Lhat D, ∀ n, 0 < n → x - 1 ⊗ₜ a n ∈ mulSub D n := by
  obtain ⟨k, ⟨b⟩⟩ := exists_basis D
  have hz : ∀ i, ∃ z : Zhat, ∀ n : ℕ+, Zhat.red n z = b.repr (a n) i := fun i =>
    exists_zhat (fun n => b.repr (a n) i) fun m n ⟨d, hd⟩ => by
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      obtain ⟨c, hc⟩ := ha m d m.2 hd0
      rw [hd, ← Finsupp.sub_apply, ← map_sub, hc]
      simp
  choose z hz using hz
  refine ⟨∑ i, z i ⊗ₜ b i, fun n hn => ?_⟩
  rw [← b.sum_repr (a n), TensorProduct.tmul_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨w, hw⟩ := exists_eq_mul (n := ⟨n, hn⟩) (z := z i - b.repr (a n) i)
    (by rw [map_sub, map_intCast]; exact sub_eq_zero.2 (hz i ⟨n, hn⟩))
  refine mem_mulSub.2 ⟨w ⊗ₜ b i, ?_⟩
  rw [TensorProduct.smul_tmul', smul_eq_mul, ← TensorProduct.smul_tmul, ← TensorProduct.sub_tmul, zsmul_one, hw]
  rfl

theorem mulSub_mul_le (n m : ℕ) : mulSub D (n * m) ≤ mulSub D n := fun x hx => by
  obtain ⟨y, rfl⟩ := mem_mulSub.1 hx
  exact mem_mulSub.2 ⟨(m : Zhat) • y, by rw [Nat.cast_mul, mul_smul]⟩

theorem hatMul_tmul (c : 𝓞 E) (a : D.La) : hatMul D c (1 ⊗ₜ a) = 1 ⊗ₜ (c • a) := by
  rw [hatMul, LinearMap.baseChange_tmul]; rfl

theorem hatForm_tmul (a b : D.La) : hatForm D (1 ⊗ₜ a) (1 ⊗ₜ b) = (D.EF a b : ℤ) := by simp [hatForm]

theorem red_hatForm {n : ℕ+} {x y : Lhat D} {a b : D.La} (hx : x - 1 ⊗ₜ a ∈ mulSub D n)
    (hy : y - 1 ⊗ₜ b ∈ mulSub D n) : Zhat.red n (hatForm D x y) = (D.EF a b : ℤ) := by
  obtain ⟨u, hu⟩ := mem_mulSub.1 hx
  obtain ⟨v, hv⟩ := mem_mulSub.1 hy
  rw [sub_eq_iff_eq_add] at hu hv
  rw [hu, hv]
  simp [hatForm_tmul]

theorem endo_ext {φ ψ : Lhat D →ₗ[Zhat] Lhat D} (h : ∀ n, 0 < n → ∀ a, φ (1 ⊗ₜ a) - ψ (1 ⊗ₜ a) ∈ mulSub D n) :
    φ = ψ :=
  LinearMap.ext fun x => sub_eq_zero.1 (eq_zero_of_mem fun n hn => mem_of_tmul _ (φ - ψ) (h n hn) x)

theorem exists_endo (f : ℕ → D.La →ₗ[𝓞 E] D.La)
    (hf : ∀ n m, 0 < n → 0 < m → ∀ a, D.ModN n (f (n * m) a - f n a)) :
    ∃ φ : Lhat D →ₗ[Zhat] Lhat D, ∀ n, 0 < n → ∀ a, φ (1 ⊗ₜ a) - 1 ⊗ₜ f n a ∈ mulSub D n := by
  choose x hx using fun a => exists_limit (fun n => f n a) fun n m hn hm => hf n m hn hm a
  let χ : D.La →+ Lhat D := AddMonoidHom.mk' x fun a b => sub_eq_zero.1 (eq_zero_of_mem fun n hn => by
    convert Submodule.sub_mem _ (hx (a + b) n hn) (Submodule.add_mem _ (hx a n hn) (hx b n hn)) using 1
    rw [map_add, TensorProduct.tmul_add]; abel)
  exact ⟨LinearMap.liftBaseChange Zhat χ.toIntLinearMap, fun n hn a => by simpa [χ] using hx a n hn⟩

theorem exists_lift (φ : Lhat D →ₗ[Zhat] Lhat D) (hφ : ∀ c x, φ (hatMul D c x) = hatMul D c (φ x)) {n : ℕ}
    (hn : 0 < n) : ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, φ (1 ⊗ₜ a) - 1 ⊗ₜ f a ∈ mulSub D n := by
  haveI := D.proj
  choose c hc using fun a : D.La => exists_approx hn (φ (1 ⊗ₜ a))
  let P := Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)
  have key : ∀ u v : D.La, P.mkQ u = P.mkQ v ↔ (1 : Zhat) ⊗ₜ[ℤ] u - 1 ⊗ₜ v ∈ mulSub D n := fun u v => by
    rw [← TensorProduct.tmul_sub, tmul_mem_mulSub_iff hn, modN_iff]
    exact Submodule.Quotient.eq _
  let F : D.La →ₗ[𝓞 E] D.La ⧸ P :=
    { toFun := fun a => P.mkQ (c a)
      map_add' := fun a b => by
        rw [← map_add, key]
        convert Submodule.sub_mem _ (Submodule.add_mem _ (hc a) (hc b)) (hc (a + b)) using 1
        rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add]; abel
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key]
        convert Submodule.sub_mem _ (map_mem_mulSub (hatMul D r) (hc a)) (hc (r • a)) using 1
        rw [map_sub, ← hφ, hatMul_tmul, hatMul_tmul]; abel }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property P.mkQ F P.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h1 := (key _ _).1 (LinearMap.congr_fun hf a)
  convert Submodule.sub_mem _ (hc a) h1 using 1
  abel

def Matches (g : Sim D) (u : Lhat D ≃ₗ[Zhat] Lhat D) : Prop :=
  ∀ n, 0 < n → ∀ a, u (1 ⊗ₜ a) - 1 ⊗ₜ g.f n a ∈ mulSub D n

def IsSimil (u : Lhat D ≃ₗ[Zhat] Lhat D) (ν : Zhatˣ) : Prop :=
  (∀ c x, u (hatMul D c x) = hatMul D c (u x)) ∧ ∀ x y, hatForm D (u x) (u y) = ν * hatForm D x y

theorem Matches.unique {g : Sim D} {u u' : Lhat D ≃ₗ[Zhat] Lhat D} (h : Matches g u) (h' : Matches g u') : u = u' :=
  LinearEquiv.toLinearMap_injective (endo_ext fun n hn a => by
    convert Submodule.sub_mem _ (h n hn a) (h' n hn a) using 1
    simp)

theorem comp_eq_id {f f' : ℕ → D.La →ₗ[𝓞 E] D.La} {φ φ' : Lhat D →ₗ[Zhat] Lhat D}
    (h : ∀ n, 0 < n → ∀ a, φ (1 ⊗ₜ a) - 1 ⊗ₜ f n a ∈ mulSub D n)
    (h' : ∀ n, 0 < n → ∀ a, φ' (1 ⊗ₜ a) - 1 ⊗ₜ f' n a ∈ mulSub D n)
    (e : ∀ n, 0 < n → ∀ a, D.ModN n (f n (f' n a) - a)) : φ ∘ₗ φ' = LinearMap.id :=
  endo_ext fun n hn a => by
    convert Submodule.add_mem _ (Submodule.add_mem _ (map_mem_mulSub φ (h' n hn a)) (h n hn (f' n a)))
      (tmul_mem_mulSub (e n hn a)) using 1
    simp [TensorProduct.tmul_sub]

theorem exists_matches (hpq : 1 ≤ D.p + D.q) (g : Sim D) :
    ∃ (u : Lhat D ≃ₗ[Zhat] Lhat D) (ν : Zhatˣ), Matches g u ∧ IsSimil u ν ∧ ∀ n, Zhat.red n ν = g.ν n := by
  obtain ⟨a₀, b₀, hab⟩ := SimAlg.exists_form_eq_one hpq
  obtain ⟨g', hg'⟩ := SimAlg.exists_inv g hab
  obtain ⟨φ, hφ⟩ := exists_endo g.f g.tower
  obtain ⟨φ', hφ'⟩ := exists_endo g'.f g'.tower
  have hz : ∀ g : Sim D, ∃ z : Zhat, ∀ n : ℕ+, Zhat.red n z = g.ν n := fun g =>
    exists_zhat (fun n => g.ν n) fun m n ⟨d, hd⟩ => by
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      rw [hd]
      exact SimAlg.dvd_mult_tower g m.2 hd0 hab
  obtain ⟨z, hz₁⟩ := hz g
  obtain ⟨z', hz₂⟩ := hz g'
  have hzz : z * z' = 1 := zhat_ext fun n => by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hg' n n.2).2
    rw [map_mul, hz₁, hz₂, map_one, ← sub_eq_zero]
    exact_mod_cast this
  refine ⟨LinearEquiv.ofLinear φ φ' (comp_eq_id hφ hφ' fun n hn a => ((hg' n hn).1 a).2)
    (comp_eq_id hφ' hφ fun n hn a => ((hg' n hn).1 a).1), Units.mkOfMulEqOne z z' hzz, hφ, ⟨fun c x => ?_, ?_⟩, hz₁⟩
  · refine LinearMap.congr_fun (endo_ext (φ := φ ∘ₗ hatMul D c) (ψ := hatMul D c ∘ₗ φ) fun n hn a => ?_) x
    convert Submodule.sub_mem _ (hφ n hn (c • a)) (map_mem_mulSub (hatMul D c) (hφ n hn a)) using 1
    simp [hatMul_tmul]
  · intro x y
    have := mem_of_tmul ⊥ ((hatForm D).compl₁₂ φ φ - z • hatForm D) (fun a => (Submodule.mem_bot _).2
      (LinearMap.ext fun y => (Submodule.mem_bot _).1 (mem_of_tmul ⊥ _ (fun b => (Submodule.mem_bot _).2 (by
        refine zhat_ext fun n => ?_
        have h1 := red_hatForm (hφ n n.2 a) (hφ n n.2 b)
        have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (g.mult n n.2 a b)
        simp only [LinearMap.sub_apply, LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_mul,
          h1, hz₁, hatForm_tmul, map_intCast, map_zero]
        exact_mod_cast h2)) y))) x
    have h3 := LinearMap.congr_fun ((Submodule.mem_bot _).1 this) y
    exact sub_eq_zero.1 h3

theorem exists_sim {u : Lhat D ≃ₗ[Zhat] Lhat D} {ν : Zhatˣ} (hu : IsSimil u ν) : ∃ g : Sim D, Matches g u := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, u (1 ⊗ₜ a) - 1 ⊗ₜ f a ∈ mulSub D n := fun n => by
    by_cases hn : 0 < n
    · exact (exists_lift u.toLinearMap hu.1 hn).imp fun _ h _ => h
    · exact ⟨0, fun h => absurd h hn⟩
  have h2 : ∀ n : ℕ, ∃ k : ℤ, ∀ hn : 0 < n, (k : ZMod n) = Zhat.red ⟨n, hn⟩ ν := fun n => by
    by_cases hn : 0 < n
    · exact (ZMod.intCast_surjective (n := n) (Zhat.red ⟨n, hn⟩ ν)).imp fun _ h _ => h
    · exact ⟨0, fun h => absurd h hn⟩
  choose f hf using h1
  choose k hk using h2
  refine ⟨⟨f, k, fun n m hn hm a => ?_, fun n hn => ?_, fun n hn a b => ?_⟩, hf⟩
  · rw [← tmul_mem_mulSub_iff hn]
    convert Submodule.sub_mem _ (hf n hn a) (mulSub_mul_le n m (hf _ (Nat.mul_pos hn hm) a)) using 1
    simp [TensorProduct.tmul_sub]
  · obtain ⟨f', hf'⟩ := exists_lift u.symm.toLinearMap (fun c x => u.injective (by simp [hu.1])) hn
    refine ⟨f', fun a => ⟨?_, ?_⟩⟩
    · rw [← tmul_mem_mulSub_iff hn, ← Submodule.neg_mem_iff]
      convert Submodule.add_mem _ (map_mem_mulSub u.symm.toLinearMap (hf n hn a)) (hf' (f n a)) using 1
      simp [TensorProduct.tmul_sub]
    · rw [← tmul_mem_mulSub_iff hn, ← Submodule.neg_mem_iff]
      convert Submodule.add_mem _ (map_mem_mulSub u.toLinearMap (hf' a)) (hf n hn (f' a)) using 1
      simp [TensorProduct.tmul_sub]
  · have h3 := red_hatForm (n := ⟨n, hn⟩) (hf n hn a) (hf n hn b)
    rw [hu.2, map_mul, hatForm_tmul, map_intCast] at h3
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, hk n hn, sub_eq_zero]
    exact h3.symm

theorem IsSimil.unique (hpq : 1 ≤ D.p + D.q) {u : Lhat D ≃ₗ[Zhat] Lhat D} {ν ν' : Zhatˣ} (h : IsSimil u ν)
    (h' : IsSimil u ν') : ν = ν' := by
  obtain ⟨a, b, hab⟩ := SimAlg.exists_form_eq_one hpq
  have := (h.2 (1 ⊗ₜ a) (1 ⊗ₜ b)).symm.trans (h'.2 _ _)
  rw [hatForm_tmul, hab] at this
  exact Units.ext (by simpa using this)

theorem Matches.congr_iff {g : Sim D} {u : Lhat D ≃ₗ[Zhat] Lhat D} (h : Matches g u) {n : ℕ} (hn : 0 < n)
    {𝔞 : Ideal (𝓞 E)} (h𝔞 : (n : 𝓞 E) ∈ 𝔞) (a b : D.La) :
    u (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D 𝔞 ↔ g.f n a - b ∈ 𝔞 • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← tmul_mem_hatSub hn h𝔞, TensorProduct.tmul_sub, ← sub_add_sub_cancel _ (1 ⊗ₜ g.f n a),
    Submodule.add_mem_iff_right _ (mulSub_le h𝔞 (h n hn a))]

theorem Matches.congSub_iff {g : Sim D} {u : Lhat D ≃ₗ[Zhat] Lhat D} (h : Matches g u) {n : ℕ} (hn : 0 < n)
    {𝔞 : Ideal (𝓞 E)} (h𝔞 : (n : 𝓞 E) ∈ 𝔞) :
    u ∈ congSub D 𝔞 ↔ ∀ a, g.f n a - a ∈ 𝔞 • (⊤ : Submodule (𝓞 E) D.La) :=
  ⟨fun k a => (h.congr_iff hn h𝔞 a a).1 (k _), fun k x =>
    mem_of_tmul (hatSub D 𝔞) (u.toLinearMap - LinearMap.id) (fun a => (h.congr_iff hn h𝔞 a a).2 (k a)) x⟩

theorem level_pos (l : Level H) : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

theorem level_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf h).1

theorem Matches.trivAt_iff {g : Sim D} {u : Lhat D ≃ₗ[Zhat] Lhat D} (h : Matches g u) (l : Level H) :
    g.TrivAt l ↔ u ∈ trivAt D l := by
  rw [trivAt, Subgroup.mem_inf, h.congSub_iff (level_pos l) (level_mem l),
    h.congSub_iff l.A_pos (Ideal.mem_span_singleton_self _)]
  simp only [Sim.TrivAt, modN_iff]

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {l l₂ : Level H}

section

variable {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := by
  rw [← sub_add_cancel x y, o.eta_add, o.eta_ker _ h, _root_.one_mul]

theorem etaA_congr (o : Obj D l b s) {x y : D.La}
    (h : x - y ∈ Ideal.span {(l.A : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)) : o.etaA x = o.etaA y := by
  obtain ⟨c, hc⟩ := modN_iff.2 h
  rw [← sub_add_cancel x y, o.etaA_add, hc, o.etaA_ker, _root_.one_mul]

end

theorem isReduced (Xo : Moduli D l) : IsReduced Xo.X := by
  haveI := Xo.smooth
  exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim _)).1

theorem map_mem_hatSub {u : Lhat D ≃ₗ[Zhat] Lhat D} (hu : ∀ c x, u (hatMul D c x) = hatMul D c (u x))
    {𝔞 : Ideal (𝓞 E)} {x : Lhat D} (hx : x ∈ hatSub D 𝔞) : u x ∈ hatSub D 𝔞 := by
  have : hatSub D 𝔞 ≤ (hatSub D 𝔞).comap u.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨a, ha, rfl⟩
    show u (1 ⊗ₜ a) ∈ hatSub D 𝔞
    refine Submodule.smul_induction_on ha (fun c hc a _ => ?_) fun a b ha hb => ?_
    · rw [← hatMul_tmul, hu]
      refine mem_of_tmul _ _ (fun b => ?_) _
      rw [hatMul_tmul]
      exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul hc trivial, rfl⟩
    · rw [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ ha hb)
  exact this hx

theorem exists_mid {u u' : Lhat D ≃ₗ[Zhat] Lhat D} (hu : ∀ c x, u (hatMul D c x) = hatMul D c (u x)) {n : ℕ}
    (hn : 0 < n) {𝔞 : Ideal (𝓞 E)} (h𝔞 : (n : 𝓞 E) ∈ 𝔞) {a b : D.La}
    (h : (u * u') (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D 𝔞) :
    ∃ c : D.La, u' (1 ⊗ₜ a) - 1 ⊗ₜ c ∈ hatSub D 𝔞 ∧ u (1 ⊗ₜ c) - 1 ⊗ₜ b ∈ hatSub D 𝔞 := by
  obtain ⟨c, hc⟩ := exists_approx hn (u' (1 ⊗ₜ a))
  refine ⟨c, mulSub_le h𝔞 hc, ?_⟩
  convert Submodule.sub_mem _ h (map_mem_hatSub hu (mulSub_le h𝔞 hc)) using 1
  simp

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem spMap_inclusion_self {F : IntermediateField ℚ ℂ} (h : F ≤ F) :
    spMap (IntermediateField.inclusion h).toRingHom = 𝟙 _ := spMap_id F

theorem levelMapF_snd (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X}
    (hπ : IsOver h Xo Xo₂ π) (c : Coeff l₂) : levelMapF h hπ c ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem snd_eq (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X} (hπ : IsOver h Xo Xo₂ π)
    (c : Coeff l₂) {T : Scheme.{0}} {x y : T ⟶ Xo₂.XF c} (e : y ≫ levelMapF h hπ c = x ≫ levelMapF h hπ c) :
    y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ := by
  rw [← levelMapF_snd h hπ c]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.snd _ _) e).trans (Category.assoc _ _ _))

theorem eq_inclusion (h : l.Dvd l₂) {j : KA l →+* KA l₂} (hj : ∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    j = (IntermediateField.inclusion (KA_le h)).toRingHom :=
  RingHom.ext fun x => Subtype.ext ((hj x).trans (IntermediateField.coe_inclusion (KA_le h) x).symm)

end Geometry

end GlobalTheory.LevelCompare

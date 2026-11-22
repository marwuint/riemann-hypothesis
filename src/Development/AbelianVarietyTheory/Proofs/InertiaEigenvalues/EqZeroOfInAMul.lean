import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal GlobalTheory.Prism IsLocalRing Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AinfK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

abbrev W0 : Type := Wq l (fK K)

scoped instance algWA : Algebra (W0 K) (Ainf l) := (wA l (fK K)).toRingHom.toAlgebra

scoped instance algWO : Algebra (W0 K) ↥(OL K) := (thetaW (fK K) K).toRingHom.toAlgebra

scoped instance towWO : IsScalarTower ℤ_[l] (W0 K) ↥(OL K) :=
  IsScalarTower.of_algebraMap_eq fun z => ((thetaW (fK K) K).commutes z).symm

scoped instance finiteWO : Module.Finite (W0 K) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _

theorem thetaW_injective : Function.Injective (thetaW (fK K) K) := fun x y h =>
  GlobalTheory.TameFrob.iotaO_injective l (fK K) ((algebraMap (Om l) ℂ_[l]).injective (by
    have h1 := congrArg (intToOC K) h
    rw [intToOC_thetaW, intToOC_thetaW, ← intToOC_thetaW _ (unrExt l (fK K)),
      ← intToOC_thetaW _ (unrExt l (fK K))] at h1
    exact congrArg Subtype.val h1))

scoped instance freeWO : Module.Free (W0 K) ↥(OL K) := by
  have : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)
  infer_instance

def AK : Type := Ainf l ⊗[W0 K] ↥(OL K)

instance : CommRing (AK K) := inferInstanceAs (CommRing (Ainf l ⊗[W0 K] ↥(OL K)))

instance : Algebra (Ainf l) (AK K) := inferInstanceAs (Algebra (Ainf l) (Ainf l ⊗[W0 K] ↥(OL K)))

instance : Algebra ↥(OL K) (AK K) :=
  (Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Ainf l ⊗[W0 K] ↥(OL K)).toRingHom.toAlgebra

instance : Module.Free (Ainf l) (AK K) := inferInstanceAs (Module.Free (Ainf l) (Ainf l ⊗[W0 K] ↥(OL K)))

instance : Module.Finite (Ainf l) (AK K) := inferInstanceAs (Module.Finite (Ainf l) (Ainf l ⊗[W0 K] ↥(OL K)))

abbrev inA : Ainf l →+* AK K := algebraMap (Ainf l) (AK K)

abbrev inO : ↥(OL K) →+* AK K := algebraMap ↥(OL K) (AK K)

theorem tmul_eq (a : Ainf l) (c : ↥(OL K)) : (show AK K from a ⊗ₜ[W0 K] c) = inA K a * inO K c := by
  change a ⊗ₜ[W0 K] c = (a ⊗ₜ[W0 K] (1 : ↥(OL K))) * ((1 : Ainf l) ⊗ₜ[W0 K] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem inA_wA (w : W0 K) : inA K (wA l (fK K) w) = inO K (thetaW (fK K) K w) :=
  ((Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Ainf l ⊗[W0 K] ↥(OL K)).commutes w).symm

variable {K} in

@[elab_as_elim] theorem induction_on {p : AK K → Prop} (x : AK K) (mul : ∀ a c, p (inA K a * inO K c))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  TensorProduct.induction_on (motive := p) x (by
    have := mul 0 0; rwa [map_zero, zero_mul] at this) (fun a c => by
    have := mul a c; rwa [← tmul_eq] at this) add

variable {K} in

theorem ringHom_ext {S : Type*} [CommRing S] {u v : AK K →+* S} (hA : ∀ a, u (inA K a) = v (inA K a))
    (hO : ∀ c, u (inO K c) = v (inO K c)) : u = v :=
  RingHom.ext fun x => induction_on x (fun a c => by rw [map_mul, map_mul, hA, hO])
    fun x y hx hy => by rw [map_add, map_add, hx, hy]

section Lift

variable {K} {S : Type*} [CommRing S] (u : Ainf l →+* S) (v : ↥(OL K) →+* S)
  (h : ∀ w : W0 K, u (wA l (fK K) w) = v (thetaW (fK K) K w))

def lift : AK K →+* S :=
  letI : Algebra (W0 K) S := (u.comp (wA l (fK K)).toRingHom).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := u, commutes' := fun _ => rfl }
    { toRingHom := v, commutes' := fun w => (h w).symm }).toRingHom

@[simp] theorem lift_inA (a : Ainf l) : lift u v h (inA K a) = u a := by
  change u a * v 1 = u a
  rw [map_one, mul_one]

@[simp] theorem lift_inO (c : ↥(OL K)) : lift u v h (inO K c) = v c := by
  change u 1 * v c = v c
  rw [map_one, one_mul]

end Lift

variable {K} in

def mapA (s : Ainf l →+* Ainf l) (hs : ∀ w : W0 K, s (wA l (fK K) w) = wA l (fK K) w) : AK K →ₐ[↥(OL K)] AK K where
  toRingHom := lift ((inA K).comp s) (inO K) fun w => by rw [RingHom.comp_apply, hs, inA_wA]
  commutes' c := lift_inO _ _ _ c

variable {K} in
theorem mapA_inA (s : Ainf l →+* Ainf l) (hs : ∀ w : W0 K, s (wA l (fK K) w) = wA l (fK K) w) (a : Ainf l) :
    mapA s hs (inA K a) = inA K (s a) :=
  lift_inA ((inA K).comp s) (inO K) (fun w => by rw [RingHom.comp_apply, hs, inA_wA]) a

variable {K}

theorem σA_wA (g : ↥(GK K)) (w : W0 K) : Per.σA (g : GQ l) (wA l (fK K) w) = wA l (fK K) w :=
  gal_wA l _ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (HasUnr.le hx)) w

def galHom (g : ↥(GK K)) : AK K →ₐ[↥(OL K)] AK K := mapA (Per.σA (g : GQ l)) (σA_wA g)

theorem galHom_inA (g : ↥(GK K)) (a : Ainf l) : galHom g (inA K a) = inA K (Per.σA (g : GQ l) a) :=
  mapA_inA _ _ a

theorem galHom_one (x : AK K) : galHom (1 : ↥(GK K)) x = x :=
  RingHom.congr_fun (ringHom_ext (u := (galHom (1 : ↥(GK K))).toRingHom) (v := RingHom.id _)
    (fun a => (galHom_inA 1 a).trans (congrArg (inA K) (GlobalTheory.RingBasics.σA_one a))) fun c => (galHom 1).commutes c) x

theorem galHom_mul (g h : ↥(GK K)) (x : AK K) : galHom (g * h) x = galHom g (galHom h x) :=
  RingHom.congr_fun (ringHom_ext (u := (galHom (g * h)).toRingHom)
    (v := (galHom g).toRingHom.comp (galHom h).toRingHom)
    (fun a => by
      change galHom (g * h) _ = galHom g (galHom h _)
      rw [galHom_inA, galHom_inA, galHom_inA, Subgroup.coe_mul, GlobalTheory.RingBasics.σA_mul]) fun c => by simp) x

variable (K) in

def gal : ↥(GK K) →* (AK K ≃ₐ[↥(OL K)] AK K) where
  toFun g := AlgEquiv.ofAlgHom (galHom g) (galHom g⁻¹)
    (AlgHom.ext fun x => by rw [AlgHom.comp_apply, ← galHom_mul, mul_inv_cancel, galHom_one]; rfl)
    (AlgHom.ext fun x => by rw [AlgHom.comp_apply, ← galHom_mul, inv_mul_cancel, galHom_one]; rfl)
  map_one' := AlgEquiv.ext galHom_one
  map_mul' g h := AlgEquiv.ext (galHom_mul g h)

theorem gal_inA (g : ↥(GK K)) (a : Ainf l) : gal K g (inA K a) = inA K (Per.σA (g : GQ l) a) := galHom_inA g a

theorem gal_inO (g : ↥(GK K)) (c : ↥(OL K)) : gal K g (inO K c) = inO K c := (gal K g).commutes c

variable (K) in

def thetaK : AK K →+* OC l := lift (Per.θ l) (intToOC K) fun w => (intToOC_thetaW _ K w).symm

theorem thetaK_inA (a : Ainf l) : thetaK K (inA K a) = Per.θ l a := lift_inA _ _ _ a

theorem thetaK_inO (c : ↥(OL K)) : thetaK K (inO K c) = intToOC K c := lift_inO _ _ _ c

variable (K) in

theorem exists_resInv : ∃ r : ResidueField ↥(OL K) →+* Fq l (fK K),
    ∀ w : W0 K, r (residue _ (thetaW (fK K) K w)) = w.coeff 0 := by
  let φ : W0 K →+* ResidueField ↥(OL K) := (residue _).comp (thetaW (fK K) K).toRingHom
  have hs : Function.Surjective φ := fun y =>
    (residue_surjective y).elim fun x hx => hx ▸ exists_thetaW (card_res K) x
  have hk : RingHom.ker φ ≤ RingHom.ker (WittVector.constantCoeff : W0 K →+* Fq l (fK K)) := fun w hw => by
    by_contra h
    exact ((WittVector.isUnit_of_coeff_zero_ne_zero w h).map φ).ne_zero hw
  exact ⟨φ.liftOfSurjective hs ⟨_, hk⟩, fun w => φ.liftOfSurjective_comp_apply hs ⟨_, hk⟩ w⟩

variable (K) in

def resO : ↥(OL K) →+* Fq l (fK K) := (exists_resInv K).choose.comp (residue _)

theorem resO_thetaW (w : W0 K) : resO K (thetaW (fK K) K w) = w.coeff 0 := (exists_resInv K).choose_spec w

theorem resO_eq_zero_iff (c : ↥(OL K)) : resO K c = 0 ↔ ¬ IsUnit c := by
  rw [resO, RingHom.comp_apply, map_eq_zero, residue_eq_zero_iff]
  rfl

variable (K) in

def red : AK K →+* OCb l :=
  lift WittVector.constantCoeff ((Fq.val l (fK K)).comp (resO K)) fun w => by
    rw [RingHom.comp_apply, resO_thetaW]; rfl

theorem red_inA (a : Ainf l) : red K (inA K a) = a.coeff 0 := lift_inA _ _ _ a

theorem red_teich (x : OCb l) : red K (inA K (WittVector.teichmuller l x)) = x := by
  rw [red_inA, WittVector.teichmuller_coeff_zero]

theorem red_inO (c : ↥(OL K)) : red K (inO K c) = Fq.val l (fK K) (resO K c) := lift_inO _ _ _ c

theorem red_inO_eq_zero {c : ↥(OL K)} (hc : ¬ IsUnit c) : red K (inO K c) = 0 := by
  rw [red_inO, (resO_eq_zero_iff c).2 hc, map_zero]

section Unif

variable {π : ↥(OL K)} (hπ : Irreducible π)
include hπ

theorem dvd_of_not_isUnit {c : ↥(OL K)} (hc : ¬ IsUnit c) : π ∣ c := by
  rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
  exact hc

theorem dvd_l : inO K π ∣ (l : AK K) := by
  simpa using map_dvd (inO K) (dvd_of_not_isUnit hπ (l_mem_max K))

theorem exists_l_dvd_pow : ∃ n : ℕ, (l : ↥(OL K)) ∣ π ^ (n + 1) := by
  obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (x := (l : ↥(OL K))) (Nat.cast_ne_zero.2 hl.out.ne_zero) hπ
  exact ⟨n, h.dvd.trans (pow_dvd_pow _ n.le_succ)⟩

theorem exists_inA (x : AK K) : ∃ a y, x = inA K a + inO K π * y :=
  induction_on x (fun a c => by
    obtain ⟨w, hw⟩ := exists_thetaW (card_res K) c
    rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at hw
    obtain ⟨d, hd⟩ := dvd_of_not_isUnit hπ hw
    refine ⟨a * wA l (fK K) w, inA K a * inO K d, ?_⟩
    rw [map_mul, inA_wA, sub_eq_iff_eq_add.1 hd, map_add, map_mul]
    ring)
    fun x y ⟨a, z, h⟩ ⟨a', z', h'⟩ => ⟨a + a', z + z', by rw [h, h', map_add]; ring⟩

theorem ker_red : RingHom.ker (red K) = Ideal.span {inO K π} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨a, y, rfl⟩ := exists_inA hπ x
    rw [RingHom.mem_ker, map_add, map_mul, red_inO_eq_zero hπ.not_isUnit, zero_mul, add_zero, red_inA,
      ← WittVector.constantCoeff_apply, ← RingHom.mem_ker, WittVector.ker_constantCoeff,
      Ideal.mem_span_singleton] at hx
    refine Ideal.mem_span_singleton.2 (dvd_add ((dvd_l hπ).trans ?_) (dvd_mul_right _ _))
    simpa using map_dvd (inA K) hx
  · rw [Ideal.span_singleton_le_iff_mem]
    exact red_inO_eq_zero hπ.not_isUnit

theorem red_eq_iff (x y : AK K) : red K x = red K y ↔ inO K π ∣ x - y := by
  rw [← Ideal.mem_span_singleton, ← ker_red hπ, RingHom.mem_ker, map_sub, sub_eq_zero]

theorem exists_teich_add (x : AK K) : ∃ y, x = inA K (WittVector.teichmuller l (red K x)) + inO K π * y := by
  obtain ⟨y, hy⟩ := (red_eq_iff hπ x _).1 (red_teich (red K x)).symm
  exact ⟨y, by rw [← hy]; ring⟩

theorem dvd_thetaK_sub (x : AK K) : intToOC K π ∣ thetaK K x - (red K x).untilt := by
  obtain ⟨y, hy⟩ := exists_teich_add hπ x
  refine ⟨thetaK K y, ?_⟩
  conv_lhs => enter [1]; rw [hy]
  rw [map_add, map_mul, thetaK_inA, thetaK_inO, WittVector.fontaineTheta_teichmuller, add_sub_cancel_left]

omit hπ in

theorem eq_zero_of_inA_mul {a : Ainf l} (ha : a ≠ 0) {x : AK K} (h : inA K a * x = 0) : x = 0 := by
  rw [← Algebra.smul_def] at h
  refine (Module.Free.chooseBasis (Ainf l) (AK K)).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis (Ainf l) (AK K)).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (mul_eq_zero.1 h1).resolve_left ha

theorem eq_zero_of_mul_pi (x : AK K) (h : x * inO K π = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := dvd_l hπ
  refine eq_zero_of_inA_mul (a := (l : Ainf l)) (WittVector.p_nonzero l _) ?_
  rw [map_natCast, hc]
  linear_combination c * h

omit hπ in
variable (K) in

theorem complete_l : IsAdicComplete (Ideal.span {(l : AK K)}) (AK K) := by
  have h := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis (W0 K) ↥(OL K)) (l : Ainf l)
  let e : ↥(OL K) ⊗[W0 K] Ainf l ≃+* AK K := (Algebra.TensorProduct.comm (W0 K) ↥(OL K) (Ainf l)).toRingEquiv
  rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton] at h
  have e1 : e ((1 : ↥(OL K)) ⊗ₜ[W0 K] (l : Ainf l)) = (l : AK K) := map_natCast (inA K) l
  rwa [e1] at h

omit hπ hl in

theorem complete_of_le {A : Type*} [CommRing A] {I J : Ideal A} {N : ℕ} (h : I ^ (N + 1) ≤ J) (hJ : J ≤ I)
    [IsAdicComplete J A] : IsAdicComplete I A where
  haus' x hx := IsHausdorff.haus' (I := J) x fun n => by
    have := hx ((N + 1) * n)
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, pow_mul] at this ⊢
    exact Ideal.pow_right_mono h n this
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => f ((N + 1) * n)) fun {m n} hmn => by
      simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have := hf (Nat.mul_le_mul_left (N + 1) hmn)
      rw [pow_mul] at this
      exact Ideal.pow_right_mono h m this
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
    simpa using add_mem h1 (Ideal.pow_right_mono hJ n (hL n))

theorem complete_pi : IsAdicComplete (Ideal.span {inO K π}) (AK K) := by
  obtain ⟨n, hn⟩ := exists_l_dvd_pow hπ
  have := complete_l K
  refine complete_of_le (J := Ideal.span {(l : AK K)}) (N := n) ?_
    (Ideal.span_singleton_le_span_singleton.2 (dvd_l hπ))
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  simpa using map_dvd (inO K) hn

end Unif

theorem exists_unif : ∃ π : ↥(OL K), Irreducible π := IsDiscreteValuationRing.exists_irreducible _

instance : IsDomain (AK K) := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  have := complete_pi hπ
  have : Nontrivial (AK K) := (red K).domain_nontrivial
  have key : ∀ x : AK K, x ≠ 0 → ∃ n z, x = inO K π ^ n * z ∧ red K z ≠ 0 := fun x hx => by
    by_contra h
    push Not at h
    refine hx (GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) x fun n => Ideal.mem_span_singleton.2 ?_)
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (ker_red hπ ▸ h n z hz : z ∈ Ideal.span {inO K π})
      exact ⟨w, by rw [hz, hw]; ring⟩
  have hreg : ∀ (n : ℕ) (z : AK K), inO K π ^ n * z = 0 → z = 0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun z hz => eq_zero_of_mul_pi hπ z (ih _ (by rw [← hz]; ring))
  have : NoZeroDivisors (AK K) := ⟨fun {x y} h => by
    by_contra h0
    rw [not_or] at h0
    obtain ⟨n, z, rfl, hz⟩ := key x h0.1
    obtain ⟨m, w, rfl, hw⟩ := key y h0.2
    have h1 := hreg (n + m) (z * w) (by rw [← h]; ring)
    exact mul_ne_zero hz hw (by rw [← map_mul, h1, map_zero])⟩
  exact NoZeroDivisors.to_isDomain _

section Ker

variable {π : ↥(OL K)} (hπ : Irreducible π) {p : OCb l} (hp : p.untilt = intToOC K π)

def eta (π : ↥(OL K)) (p : OCb l) : AK K := inA K (WittVector.teichmuller l p) - inO K π

include hp in
theorem thetaK_eta : thetaK K (eta π p) = 0 := by
  rw [eta, map_sub, thetaK_inA, thetaK_inO, WittVector.fontaineTheta_teichmuller, hp, sub_self]

include hπ hp in

theorem ker_step {x : AK K} (hx : thetaK K x = 0) :
    ∃ z y, thetaK K y = 0 ∧ x = eta π p * z + inO K π * y := by
  have h1 := dvd_thetaK_sub hπ x
  rw [hx, zero_sub, dvd_neg, ← hp] at h1
  obtain ⟨z, hz⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd h1
  obtain ⟨y, hy⟩ := exists_teich_add hπ x
  rw [hz, map_mul, map_mul] at hy
  have e : x = eta π p * inA K (WittVector.teichmuller l z) + inO K π * (inA K (WittVector.teichmuller l z) + y) := by
    rw [hy, eta]; ring
  refine ⟨_, _, ?_, e⟩
  have h2 := congrArg (thetaK K) e
  rw [hx, map_add, map_mul, map_mul, thetaK_eta hp, zero_mul, zero_add, thetaK_inO] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left ((map_ne_zero_iff _ (intToOC_injective K)).2 hπ.ne_zero)

include hπ hp in

theorem ker_thetaK : RingHom.ker (thetaK K) = Ideal.span {eta π p} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 (thetaK_eta hp))
  have := complete_pi hπ
  choose z y hy e using fun x : RingHom.ker (thetaK K) => ker_step hπ hp x.2
  let T : RingHom.ker (thetaK K) → RingHom.ker (thetaK K) := fun x => ⟨y x, hy x⟩
  obtain ⟨L, hL⟩ := GlobalTheory.Per.AinfComplete.summ_of_precomplete (inO K π) fun n => z (T^[n] ⟨x, hx⟩)
  have key : ∀ n, x = eta π p * ∑ i ∈ Finset.range n, inO K π ^ i * z (T^[i] ⟨x, hx⟩) +
      inO K π ^ n * (T^[n] ⟨x, hx⟩ : RingHom.ker (thetaK K)) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      linear_combination ih + inO K π ^ n * e (T^[n] ⟨x, hx⟩)
  refine Ideal.mem_span_singleton.2 ⟨L, sub_eq_zero.1
    (GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) _ fun n => ?_)⟩
  convert sub_mem (Ideal.mul_mem_right (T^[n] ⟨x, hx⟩ : RingHom.ker (thetaK K)).1 _
    (Ideal.mem_span_singleton_self (inO K π ^ n))) (Ideal.mul_mem_left _ (eta π p) (hL n)) using 1
  linear_combination key n

end Ker

end GlobalTheory.AinfK

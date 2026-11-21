import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton

open scoped TensorProduct

namespace GlobalTheory

def IsFreeRingAction (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A] : Prop :=
  ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤

namespace FreeQuotient

section Basic

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

theorem isFreeRingAction_iff_inertia_eq_bot :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsMaximal → P.inertia G = ⊥ := by
  constructor
  · intro h P hP
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    refine hP.ne_top (top_le_iff.mp ?_)
    rw [← h g hg1, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_inertia.mp hg a
  · intro h g hg
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have : g ∈ P.inertia G :=
      AddSubgroup.mem_inertia.mpr fun a ↦ hle (Ideal.subset_span ⟨a, rfl⟩)
    rw [h P hP] at this
    exact hg this

variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]

noncomputable def galoisMap : A ⊗[B] A →ₐ[A] (G → A) :=
  Algebra.TensorProduct.lift (Algebra.ofId A (G → A))
    (Pi.algHom B _ fun g ↦ MulSemiringAction.toAlgHom B A g) fun _ _ ↦ Commute.all _ _

@[simp] theorem galoisMap_tmul (a b : A) (g : G) :
    galoisMap G A B (a ⊗ₜ b) g = a * g • b := rfl

variable {G A} in

theorem exists_galoisMap_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ e : A ⊗[B] A, (∀ g ∉ H, galoisMap G A B e g = 0) ∧
      ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
  classical
  cases nonempty_fintype G
  have key : ∀ g : G, ∀ c ∈ Ideal.span (Set.range fun a : A ↦ g • a - a),
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - c ∈ P := by
    intro g c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨(g • a) ⊗ₜ 1 - 1 ⊗ₜ a, by simp, fun h hh ↦ ?_⟩
      have := P.neg_mem (hH h hh a)
      simp only [map_sub, Pi.sub_apply, galoisMap_tmul, smul_one, mul_one, one_mul]
      convert this using 1
      ring
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨e, he, he'⟩ := hx
      obtain ⟨f, hf, hf'⟩ := hy
      refine ⟨e + f, by simp [he, hf], fun h hh ↦ ?_⟩
      have := P.add_mem (he' h hh) (hf' h hh)
      simp only [map_add, Pi.add_apply]
      convert this using 1
      ring
    | smul r x _ hx =>
      obtain ⟨e, he, he'⟩ := hx
      refine ⟨r • e, by simp [he], fun h hh ↦ ?_⟩
      have := P.mul_mem_left r (he' h hh)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      convert this using 1
      ring
  have key2 : ∀ g ∉ H,
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
    intro g hg
    have h1 : (1 : A) ∈ P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) := by
      rw [hH' g hg]; trivial
    obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp h1
    obtain ⟨e, he, he'⟩ := key g c hc
    refine ⟨e, he, fun h hh ↦ ?_⟩
    have := P.sub_mem (he' h hh) hp
    rw [← hpc]
    convert this using 1
    ring
  choose! e he he' using key2
  refine ⟨∏ g ∈ Finset.univ.filter (· ∉ H), e g, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · rw [map_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (i := g) (by simpa using hg) (he g hg)
  · rw [map_prod, Finset.prod_apply, ← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one fun g hg ↦ ?_
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact he' g (by simpa using hg) h hh

variable {G A} in

theorem exists_finset_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ s : Finset (A × A), (∀ g ∉ H, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ H, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  obtain ⟨e, he, he'⟩ := exists_galoisMap_separating ℤ P H hH hH'
  obtain ⟨s, rfl⟩ := e.exists_finset
  refine ⟨s, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · simpa [Finset.sum_apply] using he g hg
  · simpa [Finset.sum_apply] using he' h hh

variable {G A} in

theorem exists_galois_coordinates [Finite G] (h : IsFreeRingAction G A) :
    ∃ s : Finset (A × A), (∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∑ p ∈ s, p.1 * p.2 = 1 := by
  obtain ⟨s, hs, hs'⟩ := exists_finset_separating (G := G) (⊥ : Ideal A) {1}
    (by rintro _ rfl a; simp) (fun g hg ↦ by rw [h g hg, sup_top_eq])
  exact ⟨s, hs, by simpa [sub_eq_zero] using hs' 1 rfl⟩

variable {G A} in

theorem exists_finset_inertia [Finite G] (P : Ideal A) [hP : P.IsMaximal] :
    ∃ s : Finset (A × A), (∀ g ∉ P.inertia G, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ P.inertia G, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  refine exists_finset_separating P (P.inertia G : Set G)
    (fun h hh ↦ AddSubgroup.mem_inertia.mp hh) fun g hg ↦ ?_
  by_contra hne
  refine hg (AddSubgroup.mem_inertia.mpr fun a ↦ ?_)
  have := hP.eq_of_le hne le_sup_left
  change g • a - a ∈ P
  rw [this]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨a, rfl⟩)

end Basic

instance smulDistribClass_self (G : Type*) [Group G] (A : Type*) [CommRing A]
    [MulSemiringAction G A] : SMulDistribClass G A A :=
  ⟨fun g a b ↦ smul_mul' g a b⟩

theorem smul_sum_smul {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    [DistribMulAction G M] (m : M) (g : G) : g • ∑ h : G, h • m = ∑ h : G, h • m := by
  simp only [Finset.smul_sum, smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft g) fun h ↦ h • m

section Trace

variable (G : Type*) [Group G] [Fintype G] (B : Type*) [CommRing B]
  (M : Type*) [AddCommGroup M] [Module B M] [DistribMulAction G M] [SMulCommClass G B M]

def moduleTrace : M →ₗ[B] (Representation.ofDistribMulAction B G M).invariants where
  toFun m := ⟨∑ g : G, g • m, fun g ↦ smul_sum_smul m g⟩
  map_add' x y := Subtype.ext (by simp [Finset.sum_add_distrib])
  map_smul' b x := Subtype.ext (by simp [Finset.smul_sum, smul_comm _ b])

@[simp] theorem coe_moduleTrace (m : M) : (moduleTrace G B M m : M) = ∑ g : G, g • m := rfl

variable (A : Type*) [CommRing A] [MulSemiringAction G A] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]

noncomputable def invariantsRingEquiv :
    B ≃ₗ[B] (Representation.ofDistribMulAction B G A).invariants :=
  LinearEquiv.ofBijective ((Algebra.linearMap B A).codRestrict
      (Representation.ofDistribMulAction B G A).invariants fun b g ↦ smul_algebraMap g b)
    ⟨fun a b hab ↦ FaithfulSMul.algebraMap_injective B A (congrArg Subtype.val hab),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨b, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) x hx
        exact ⟨b, rfl⟩⟩

omit [Fintype G] in
theorem algebraMap_invariantsRingEquiv_symm
    (x : (Representation.ofDistribMulAction B G A).invariants) :
    algebraMap B A ((invariantsRingEquiv G B A).symm x) = x :=
  congrArg Subtype.val ((invariantsRingEquiv G B A).apply_symm_apply x)

noncomputable def ringTrace : A →ₗ[B] B :=
  (invariantsRingEquiv G B A).symm.toLinearMap ∘ₗ moduleTrace G B A

@[simp] theorem algebraMap_ringTrace (a : A) :
    algebraMap B A (ringTrace G B A a) = ∑ g : G, g • a :=
  algebraMap_invariantsRingEquiv_symm G B A _

end Trace

section Tame

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

theorem sum_smul_sum_smul (s : Finset (A × A)) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = ∑ g : G, (∑ p ∈ s, p.1 * g • p.2) • g • m := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_distrib_smul, mul_smul]
  exact Finset.sum_comm

theorem exists_sum_sub_card_smul_mem (P : Ideal A) [P.IsMaximal] (m : M)
    (hm : ∀ g ∈ P.inertia G, g • m - m ∈ P • (⊤ : Submodule A M)) :
    ∃ s : Finset (A × A), ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) -
      (Nat.card (P.inertia G) : A) • m ∈ P • (⊤ : Submodule A M) := by
  classical
  obtain ⟨s, hs, hs'⟩ := exists_finset_inertia (G := G) P
  refine ⟨s, ?_⟩
  rw [sum_smul_sum_smul, ← Finset.sum_subset (Finset.filter_subset (· ∈ P.inertia G) _)
    (fun g _ hg ↦ by rw [hs g (by simpa using hg), zero_smul])]
  have : (Nat.card (P.inertia G) : A) • m =
      ∑ _g ∈ Finset.univ.filter (· ∈ P.inertia G), m := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [this, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun g hg ↦ ?_
  have hg' : g ∈ P.inertia G := by simpa using hg
  have := add_mem (Submodule.smul_mem_smul (hs' g hg') (Submodule.mem_top (x := g • m)))
    (hm g hg')
  convert this using 1
  rw [sub_smul, one_smul]
  abel

variable (G A) in

theorem exists_sum_smul_eq_one
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) :
    ∃ c : A, ∑ g : G, g • c = 1 := by
  let B := FixedPoints.subring A G
  haveI := isIntegral_fixedSubring A G
  have : LinearMap.range (ringTrace G B A) = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨P, hP, rfl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) Q
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
          exact bot_le)
    obtain ⟨s, hs⟩ := exists_sum_sub_card_smul_mem (G := G) P (1 : A) (by simp)
    rw [smul_eq_mul, Ideal.mul_top, smul_eq_mul, mul_one] at hs
    refine h P hP ((Submodule.sub_mem_iff_right _ (Ideal.sum_mem _ fun p _ ↦ ?_)).mp hs)
    refine P.mul_mem_left _ ?_
    rw [← algebraMap_ringTrace G B A]
    exact hle ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp this 1
  exact ⟨c, by rw [← algebraMap_ringTrace G B A, hc, map_one]⟩

end Tame

section DualBasis

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]

variable (G) in

def averageMap (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun m := ∑ g : G, g • f (g⁻¹ • m)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_distrib_smul]

theorem averageMap_apply (f : M →ₗ[A] N) (m : M) :
    averageMap G f m = ∑ g : G, g • f (g⁻¹ • m) := rfl

variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

end DualBasis

section Free

variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]

theorem sum_smul_sum_smul_eq [Fintype G] {M : Type*} [AddCommGroup M] [Module A M]
    [DistribMulAction G M] [SMulDistribClass G A M] {s : Finset (A × A)}
    (hs : ∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) (hs' : ∑ p ∈ s, p.1 * p.2 = 1) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = m := by
  rw [sum_smul_sum_smul, Finset.sum_eq_single 1 (fun g _ hg ↦ by rw [hs g hg, zero_smul])
    (by simp)]
  simp [hs']

theorem exists_sum_smul_eq_one_of_free [Fintype G] (h : IsFreeRingAction G A) :
    ∃ c : A, ∑ g : G, g • c = 1 :=
  exists_sum_smul_eq_one G A fun P hP ↦ by
    rw [(isFreeRingAction_iff_inertia_eq_bot G A).mp h P hP]
    simpa using (Ideal.ne_top_iff_one P).mp hP.ne_top

variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]

theorem finite_and_projective (h : IsFreeRingAction G A) :
    Module.Finite B A ∧ Module.Projective B A := by
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  have hcomp : Fintype.linearCombination B (fun p : s ↦ p.1.1) ∘ₗ
      LinearMap.pi (fun p : s ↦ ringTrace G B A ∘ₗ LinearMap.mulLeft B p.1.2) = LinearMap.id := by
    refine LinearMap.ext fun a ↦ ?_
    have := sum_smul_sum_smul_eq hs hs' a
    rw [← Finset.sum_coe_sort] at this
    simpa [Fintype.linearCombination_apply, Algebra.smul_def, mul_comm] using this
  exact ⟨.of_surjective (Fintype.linearCombination B (fun p : s ↦ p.1.1)) fun x ↦ ⟨_, LinearMap.congr_fun hcomp x⟩, .of_split _ _ hcomp⟩

theorem faithfullyFlat (h : IsFreeRingAction G A) : Module.FaithfullyFlat B A :=
  haveI := (finite_and_projective B h).1
  haveI := (finite_and_projective B h).2
  .of_comap_surjective (Algebra.IsIntegral.comap_surjective B A)

theorem bijective_galoisMap (h : IsFreeRingAction G A) :
    Function.Bijective (galoisMap G A B) := by
  classical
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  constructor
  · have key : ∀ z : A ⊗[B] A,
        ∑ p ∈ s, (∑ g : G, g • p.2 * galoisMap G A B z g) ⊗ₜ[B] p.1 = z := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul,
          hx, hy]
      | tmul a b =>
        conv_rhs => rw [← sum_smul_sum_smul_eq hs hs' b, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← algebraMap_ringTrace G B A, smul_eq_mul, mul_comm, ← Algebra.smul_def,
          ← TensorProduct.smul_tmul, Algebra.smul_def, algebraMap_ringTrace, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        simp only [galoisMap_tmul, smul_eq_mul, smul_mul']
        ring
    intro x y hxy
    rw [← key x, ← key y, hxy]
  · intro f
    refine ⟨∑ k : G, f k • ∑ p ∈ s, p.1 ⊗ₜ (k⁻¹ • p.2), funext fun g ↦ ?_⟩
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, galoisMap_tmul, smul_smul,
      smul_eq_mul]
    rw [Finset.sum_eq_single g (fun k _ hk ↦ by
      rw [hs _ (fun h ↦ hk (mul_inv_eq_one.mp h).symm), mul_zero]) (by simp)]
    simp [hs']

noncomputable def galoisEquiv (h : IsFreeRingAction G A) : A ⊗[B] A ≃ₐ[A] (G → A) :=
  AlgEquiv.ofBijective _ (bijective_galoisMap B h)

@[simp] theorem galoisEquiv_tmul (h : IsFreeRingAction G A) (a b : A) (g : G) :
    galoisEquiv B h (a ⊗ₜ b) g = a * g • b := rfl

theorem etale (h : IsFreeRingAction G A) : Algebra.Etale B A :=
  haveI := faithfullyFlat B h
  haveI : Algebra.Etale A (A ⊗[B] A) := .of_equiv (galoisEquiv B h).symm
  Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A

variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

end Free

section BaseChange

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]

instance smulDistribClass_tensorProduct : SMulDistribClass G A (A ⊗[B] N) where
  smul_distrib_smul g a z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul b n => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']

variable [SMulCommClass G B A]

noncomputable def toInvariantsTensor :
    N →ₗ[B] (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants :=
  (TensorProduct.mk B A N 1).codRestrict
    (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants fun n g ↦ by
      change g • ((1 : A) ⊗ₜ[B] n) = 1 ⊗ₜ[B] n
      rw [TensorProduct.smul_tmul', smul_one]

@[simp] theorem coe_toInvariantsTensor (n : N) :
    (toInvariantsTensor G A B N n : A ⊗[B] N) = 1 ⊗ₜ n := rfl

variable [FaithfulSMul B A] [Algebra.IsInvariant B A G]

end BaseChange

end FreeQuotient

universe w v u

open CategoryTheory

structure SemilinearModule (G : Type v) [Group G] (A : Type u) [CommRing A]
    [MulSemiringAction G A] where

  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [action : DistribMulAction G carrier]
  [semilinear : SMulDistribClass G A carrier]

namespace SemilinearModule

attribute [instance] addCommGroup module action semilinear

variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]

instance : Category (SemilinearModule.{w} G A) where
  Hom M N := {f : M.carrier →ₗ[A] N.carrier // ∀ (g : G) m, f (g • m) = g • f m}
  id _ := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f f' := ⟨f'.1 ∘ₗ f.1, fun g m ↦ by
    rw [LinearMap.comp_apply, f.2, f'.2, LinearMap.comp_apply]⟩

instance smulCommClass_fixedSubring' : SMulCommClass (FixedPoints.subring A G) G A :=
  .symm _ _ _

variable {G A}

end SemilinearModule

end GlobalTheory

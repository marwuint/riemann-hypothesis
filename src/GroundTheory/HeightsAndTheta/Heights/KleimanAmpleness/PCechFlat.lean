import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open TensorProduct MvPolynomial

noncomputable section

universe u v

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']

theorem tmul_eq_smul_one_tmul {X : Type*} [AddCommGroup X] [Module S X] (s : S') (x : X) :
    s ⊗ₜ[S] x = s • ((1 : S') ⊗ₜ[S] x) := by
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem ext_one_tmul {X Y : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S' Y]
    {u v : S' ⊗[S] X →ₗ[S'] Y} (h : ∀ x, u (1 ⊗ₜ x) = v (1 ⊗ₜ x)) (z : S' ⊗[S] X) : u z = v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [tmul_eq_smul_one_tmul, map_smul, map_smul, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']

def cokerEquiv (α : X →ₗ[S] Y) (α' : X' →ₗ[S'] Y') (eX : S' ⊗[S] X ≃ₗ[S'] X')
    (eY : S' ⊗[S] Y ≃ₗ[S'] Y') (h : ∀ x, α' (eX (1 ⊗ₜ x)) = eY (1 ⊗ₜ α x)) :
    (Y' ⧸ LinearMap.range α') ≃ₗ[S'] S' ⊗[S] (Y ⧸ LinearMap.range α) :=
  (Submodule.Quotient.equiv _ _ eY.symm (by
    have h1 : eY.symm.toLinearMap ∘ₗ α' =
        AlgebraTensorModule.lTensor S' S' α ∘ₗ eX.symm.toLinearMap := by
      apply LinearMap.ext; intro y
      obtain ⟨z, rfl⟩ := eX.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      have hz := ext_one_tmul (u := α' ∘ₗ eX.toLinearMap)
        (v := eY.toLinearMap ∘ₗ AlgebraTensorModule.lTensor S' S' α) (fun x => by simp [h]) z
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
      rw [hz, LinearEquiv.symm_apply_apply]
    have h2 : AlgebraTensorModule.lTensor S' S' α =
        AlgebraTensorModule.lTensor S' S' ((LinearMap.range α).subtype.restrictScalars S) ∘ₗ
          AlgebraTensorModule.lTensor S' S' α.rangeRestrict := by
      apply LinearMap.ext; intro z
      exact ext_one_tmul (fun x => by simp) z
    have h3 : LinearMap.range (AlgebraTensorModule.lTensor S' S' α.rangeRestrict) = ⊤ := by
      rw [LinearMap.range_eq_top, AlgebraTensorModule.coe_lTensor]
      exact LinearMap.lTensor_surjective _ (LinearMap.surjective_rangeRestrict α)
    rw [← LinearMap.range_comp, h1, LinearMap.range_comp_of_range_eq_top _ eX.symm.range, h2,
      LinearMap.range_comp_of_range_eq_top _ h3])).trans
    (AlgebraTensorModule.tensorQuotientEquiv S' S S' (LinearMap.range α)).symm

variable [Module.Flat S S']

def kerEquiv (b : X →ₗ[S] Y) (b' : X' →ₗ[S'] Y') (eX : S' ⊗[S] X ≃ₗ[S'] X')
    (eY : S' ⊗[S] Y ≃ₗ[S'] Y') (h : ∀ x, b' (eX (1 ⊗ₜ x)) = eY (1 ⊗ₜ b x)) :
    S' ⊗[S] LinearMap.ker b ≃ₗ[S'] LinearMap.ker b' :=
  (LinearMap.tensorKerEquiv S' S' b).trans (eX.ofSubmodules _ _ (by
    have hc : ∀ z, b' (eX z) = eY (AlgebraTensorModule.lTensor S' S' b z) := fun z => by
      have hz := ext_one_tmul (u := b' ∘ₗ eX.toLinearMap)
        (v := eY.toLinearMap ∘ₗ AlgebraTensorModule.lTensor S' S' b) (fun x => by simp [h]) z
      simpa using hz
    ext y
    obtain ⟨z, rfl⟩ := eX.surjective y
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker, hc,
      LinearEquiv.map_eq_zero_iff]))

def subEquiv (E : S' ⊗[S] X ≃ₗ[S'] X') (D : Submodule S X) (D' : Submodule S' X')
    (h₁ : ∀ x ∈ D, E (1 ⊗ₜ x) ∈ D')
    (h₂ : D' ≤ Submodule.span S' ((fun x => E (1 ⊗ₜ x)) '' (D : Set X))) :
    S' ⊗[S] D ≃ₗ[S'] D' :=
  (LinearEquiv.ofInjective (E.toLinearMap ∘ₗ AlgebraTensorModule.lTensor S' S' D.subtype) (by
      intro z w hzw
      have h0 : AlgebraTensorModule.lTensor S' S' D.subtype z =
          AlgebraTensorModule.lTensor S' S' D.subtype w := E.injective hzw
      rw [AlgebraTensorModule.coe_lTensor] at h0
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := S') D.subtype
        D.injective_subtype h0)).trans
    (LinearEquiv.ofEq _ _ (le_antisymm (by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s x =>
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgebraTensorModule.lTensor_tmul,
          Submodule.coe_subtype, LinearEquiv.coe_coe]
        rw [tmul_eq_smul_one_tmul, map_smul]
        exact D'.smul_mem s (h₁ x.1 x.2)
      | add a b ha hb => rw [map_add]; exact D'.add_mem ha hb)
      (h₂.trans (Submodule.span_le.mpr (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp⟩)))))

end FlatBC

namespace FlatBC

end FlatBC

namespace FlatBC

end FlatBC

namespace FlatBC

section Poly

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] (N : ℕ)

abbrev pmap : Poly S N →+* Poly S' N := MvPolynomial.map (algebraMap S S')

variable {S S' N}

theorem map_monos (I : Finset (Fin (N + 1))) :
    (monos (S := S) I).map (pmap S S' N) = monos (S := S') I := by
  rw [monos, monos, MonoidHom.map_mclosure, Set.image_image]
  simp only [pmap, MvPolynomial.map_X]

theorem pmap_mem_monos {I : Finset (Fin (N + 1))} {t : Poly S N} (ht : t ∈ monos I) :
    pmap S S' N t ∈ monos (S := S') I := by
  rw [← map_monos (S := S)]
  exact Submonoid.mem_map_of_mem _ ht

theorem exists_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S' N} (hs : s ∈ monos (S := S') I) :
    ∃ t ∈ monos (S := S) I, pmap S S' N t = s := by
  rw [← map_monos (S := S)] at hs
  exact Submonoid.mem_map.mp hs

end Poly

end FlatBC

namespace FlatBC

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}

abbrev lmk {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] (I : Finset (Fin (N + 1))) (m : M) (s : monos (S := S) I) :
    LocMod S N M I :=
  (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M)

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem lmk_psmul (I : Finset (Fin (N + 1))) (p : Poly S N) (m : M) (s : monos (S := S) I) :
    p • lmk I m s = lmk I (p • m) s :=
  LocalizedModule.smul'_mk p m s

theorem lmk_smul (I : Finset (Fin (N + 1))) (a : S) (m : M) (s : monos (S := S) I) :
    a • lmk I m s = lmk I (a • m) s := by
  show (algebraMap S (Poly S N) a) • lmk I m s = _
  rw [lmk_psmul, algebraMap_smul]

theorem lmk_add (I : Finset (Fin (N + 1))) (m m' : M) (s : monos (S := S) I) :
    lmk I m s + lmk I m' s = lmk I (m + m') s := by
  show (LocalizedModule.mk m s + LocalizedModule.mk m' s : LocalizedModule _ M) =
    LocalizedModule.mk _ _
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

theorem lmk_zero (I : Finset (Fin (N + 1))) (s : monos (S := S) I) : lmk I (0 : M) s = 0 :=
  LocalizedModule.zero_mk s

@[elab_as_elim]
theorem lmk_induction {I : Finset (Fin (N + 1))} {P : LocMod S N M I → Prop}
    (h : ∀ m s, P (lmk I m s)) (x : LocMod S N M I) : P x :=
  LocalizedModule.induction_on h x

variable {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)

include hX in
theorem map_poly_smul (p : Poly S N) (m : M) : f (p • m) = pmap S S' N p • f m := by
  revert m
  refine MvPolynomial.induction_on (motive := fun p => ∀ m : M, f (p • m) = pmap S S' N p • f m) p
    (fun a m => ?_) (fun p q hp hq m => ?_) (fun p i hp m => ?_)
  · calc f (C a • m) = f (a • m) := by
          rw [← algebraMap_smul (Poly S N) a m, MvPolynomial.algebraMap_eq]
      _ = a • f m := map_smul f a m
      _ = algebraMap S S' a • f m := (algebraMap_smul S' a (f m)).symm
      _ = (C (algebraMap S S' a) : Poly S' N) • f m := by
          rw [← algebraMap_smul (Poly S' N) (algebraMap S S' a) (f m), MvPolynomial.algebraMap_eq]
      _ = pmap S S' N (C a) • f m := by rw [MvPolynomial.map_C]
  · rw [add_smul, map_add, hp, hq, map_add, add_smul]
  · rw [mul_smul, hp, hX, map_mul, MvPolynomial.map_X, mul_smul]

omit [Module S M'] [IsScalarTower S S' M'] in
theorem smul_comm' {Y : Type*} [AddCommGroup Y] [Module (Poly S' N) Y] [Module S' Y]
    [IsScalarTower S' (Poly S' N) Y] (a : S') (p : Poly S' N) (y : Y) : a • p • y = p • a • y := by
  rw [← algebraMap_smul (Poly S' N) a (p • y), ← algebraMap_smul (Poly S' N) a y, smul_smul,
    smul_smul, mul_comm]

def gRaw (I : Finset (Fin (N + 1))) (x : LocalizedModule (monos (S := S) I) M) :
    LocalizedModule (monos (S := S') I) M' :=
  x.liftOn (fun p => LocalizedModule.mk (f p.1) ⟨pmap S S' N p.2, pmap_mem_monos p.2.2⟩)
    (fun p p' hp => by
      obtain ⟨u, hu⟩ := hp
      refine LocalizedModule.mk_eq.mpr ⟨⟨pmap S S' N u, pmap_mem_monos u.2⟩, ?_⟩
      have h1 := congrArg f hu
      simp only [Submonoid.smul_def, map_poly_smul f hX] at h1 ⊢
      exact h1)

theorem gRaw_mk (I : Finset (Fin (N + 1))) (m : M) (s : monos (S := S) I) :
    gRaw f hX I (LocalizedModule.mk m s) =
      LocalizedModule.mk (f m) ⟨pmap S S' N s, pmap_mem_monos s.2⟩ :=
  LocalizedModule.liftOn_mk _ m s

def gLoc (I : Finset (Fin (N + 1))) : LocMod S N M I →+ LocMod S' N M' I :=
  AddMonoidHom.mk' (gRaw f hX I)
    (fun x y => by
      revert y
      refine lmk_induction (fun m s => ?_) x
      intro y
      refine lmk_induction (fun m' s' => ?_) y
      show gRaw f hX I (LocalizedModule.mk m s + LocalizedModule.mk m' s') =
        gRaw f hX I (LocalizedModule.mk m s) + gRaw f hX I (LocalizedModule.mk m' s')
      rw [LocalizedModule.mk_add_mk, gRaw_mk, gRaw_mk, gRaw_mk, LocalizedModule.mk_add_mk]
      congr 1
      · simp only [map_add, Submonoid.smul_def, map_poly_smul f hX]
      · exact Subtype.ext (by simp only [Submonoid.coe_mul, map_mul]))

theorem gLoc_mk (I : Finset (Fin (N + 1))) (m : M) (s : monos (S := S) I) :
    gLoc f hX I (lmk I m s) = lmk I (f m) ⟨pmap S S' N s, pmap_mem_monos s.2⟩ :=
  gRaw_mk f hX I m s

theorem gLoc_psmul (I : Finset (Fin (N + 1))) (p : Poly S N) (x : LocMod S N M I) :
    gLoc f hX I (p • x) = pmap S S' N p • gLoc f hX I x := by
  refine lmk_induction (fun m s => ?_) x
  rw [lmk_psmul, gLoc_mk, gLoc_mk, lmk_psmul, map_poly_smul f hX]

theorem gLoc_smul (I : Finset (Fin (N + 1))) (a : S) (x : LocMod S N M I) :
    gLoc f hX I (a • x) = algebraMap S S' a • gLoc f hX I x := by
  refine lmk_induction (fun m s => ?_) x
  rw [lmk_smul I a m s, gLoc_mk, gLoc_mk, lmk_smul I (algebraMap S S' a) (f m), algebraMap_smul,
    map_smul]

theorem bij_of_tmul (hf : IsBaseChange S' f) (I : Finset (Fin (N + 1)))
    (L : S' ⊗[S] LocMod S N M I →+ LocMod S' N M' I) (hL : ∀ a x, L (a ⊗ₜ x) = a • gLoc f hX I x) :
    Function.Bijective L := by
  let tsm : Poly S N → (LocMod S N M I →ₗ[S] LocMod S N M I) := fun t =>
    (LinearMap.lsmul (Poly S N) (LocMod S N M I) t).restrictScalars S
  let msm : Poly S N → (M →ₗ[S] M) := fun t => (LinearMap.lsmul (Poly S N) M t).restrictScalars S
  let lm : M →ₗ[S] LocMod S N M I := (locMk M I).restrictScalars S
  have tsm_apply : ∀ t x, tsm t x = t • x := fun _ _ => rfl
  have msm_apply : ∀ t m, msm t m = t • m := fun _ _ => rfl
  have lm_apply : ∀ m, lm m = lmk I m 1 := fun _ => rfl
  have F3 : ∀ t, tsm t ∘ₗ lm = lm ∘ₗ msm t := fun t => LinearMap.ext fun m => by
    simp only [LinearMap.comp_apply, tsm_apply, msm_apply, lm_apply, lmk_psmul]
  have F4 : ∀ t z, L (LinearMap.lTensor S' (tsm t) z) = pmap S S' N t • L z := by
    intro t z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [LinearMap.lTensor_tmul, hL, hL, tsm_apply, gLoc_psmul, smul_comm']
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, smul_add]
  have F5 : ∀ w, L (LinearMap.lTensor S' lm w) = lmk I (hf.equiv w) 1 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, lmk_zero]
    | tmul a m =>
      rw [LinearMap.lTensor_tmul, hL, lm_apply, gLoc_mk, IsBaseChange.equiv_tmul, lmk_smul]
      congr 1
      exact Subtype.ext (map_one _)
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, lmk_add]
  have F6 : ∀ u w, hf.equiv (LinearMap.lTensor S' (msm u) w) = pmap S S' N u • hf.equiv w := by
    intro u w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, msm_apply,
        map_poly_smul f hX, smul_comm']
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, smul_add]
  have F7 : ∀ t ∈ monos (S := S) I, Function.Injective (LinearMap.lTensor S' (tsm t)) := by
    intro t ht
    have hb : Function.Bijective (tsm t) := by
      have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (monos (S := S) I) M)
        ⟨t, ht⟩
      rw [Module.End.isUnit_iff] at hu
      exact hu
    let e := LinearEquiv.ofBijective (tsm t) hb
    intro a b hab
    have h2 := congrArg (LinearMap.lTensor S' e.symm.toLinearMap) hab
    rwa [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply,
      show e.symm.toLinearMap ∘ₗ tsm t = LinearMap.id from
        LinearMap.ext fun x => e.symm_apply_apply x,
      LinearMap.lTensor_id_apply, LinearMap.lTensor_id_apply] at h2
  have cd : ∀ z, ∃ t ∈ monos (S := S) I, ∃ w,
      LinearMap.lTensor S' (tsm t) z = LinearMap.lTensor S' lm w := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, one_mem _, 0, by simp⟩
    | tmul a x =>
      refine lmk_induction (fun m s => ?_) x
      refine ⟨s, s.2, a ⊗ₜ m, ?_⟩
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, tsm_apply, lmk_psmul, lm_apply]
      congr 1
      rw [← Submonoid.smul_def]
      exact LocalizedModule.mk_cancel s m
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨t₁, ht₁, w₁, hw₁⟩ := h₁
      obtain ⟨t₂, ht₂, w₂, hw₂⟩ := h₂
      refine ⟨t₁ * t₂, mul_mem ht₁ ht₂,
        LinearMap.lTensor S' (msm t₂) w₁ + LinearMap.lTensor S' (msm t₁) w₂, ?_⟩
      have e1 : tsm (t₁ * t₂) = tsm t₂ ∘ₗ tsm t₁ := LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, tsm_apply, mul_comm t₁ t₂, mul_smul]
      have e2 : tsm (t₁ * t₂) = tsm t₁ ∘ₗ tsm t₂ := LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, tsm_apply, mul_smul]
      rw [map_add, map_add]
      congr 1
      · rw [e1, LinearMap.lTensor_comp_apply, hw₁, ← LinearMap.lTensor_comp_apply, F3,
          LinearMap.lTensor_comp_apply]
      · rw [e2, LinearMap.lTensor_comp_apply, hw₂, ← LinearMap.lTensor_comp_apply, F3,
          LinearMap.lTensor_comp_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨t, ht, w, hw⟩ := cd z
    have h1 : lmk (S := S') I (hf.equiv w) 1 = 0 := by rw [← F5, ← hw, F4, hz, smul_zero]
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp (h1.trans (lmk_zero (S := S') (M := M') I 1).symm)
    simp only [one_smul, smul_zero] at hu
    obtain ⟨u₀, hu₀, hu₀u⟩ := exists_of_mem_monos (S := S) u.2
    have h2 : LinearMap.lTensor S' (msm u₀) w = 0 := by
      apply hf.equiv.injective
      rw [F6, map_zero, hu₀u, ← Submonoid.smul_def, hu]
    have h3 : LinearMap.lTensor S' (tsm u₀) (LinearMap.lTensor S' (tsm t) z) = 0 := by
      rw [hw, ← LinearMap.lTensor_comp_apply, F3, LinearMap.lTensor_comp_apply, h2, map_zero]
    have h4 : LinearMap.lTensor S' (tsm t) z = 0 := F7 u₀ hu₀ (by rw [h3, map_zero])
    exact F7 t ht (by rw [h4, map_zero])
  · intro y
    refine lmk_induction (fun m' s' => ?_) y
    obtain ⟨t, ht, hts⟩ := exists_of_mem_monos (S := S) s'.2
    have key : ∀ z : S' ⊗[S] M, ∃ w, L w = lmk I (hf.equiv z) s' := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by rw [map_zero, map_zero, lmk_zero]⟩
      | tmul a m =>
        refine ⟨a ⊗ₜ lmk I m ⟨t, ht⟩, ?_⟩
        rw [hL, gLoc_mk, IsBaseChange.equiv_tmul, lmk_smul]
        congr 1
        exact Subtype.ext hts
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨w₁, hw₁⟩ := h₁
        obtain ⟨w₂, hw₂⟩ := h₂
        exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂, map_add, lmk_add]⟩
    obtain ⟨w, hw⟩ := key (hf.equiv.symm m')
    exact ⟨w, by rw [hw, LinearEquiv.apply_symm_apply]⟩

abbrev locModS (I : Finset (Fin (N + 1))) : Module S (LocMod S' N M' I) :=
  Module.compHom _ (algebraMap S S')

def locBC (hf : IsBaseChange S' f) (I : Finset (Fin (N + 1))) :
    S' ⊗[S] LocMod S N M I ≃ₗ[S'] LocMod S' N M' I :=
  letI := locModS (S := S) (S' := S') (N := N) (M' := M') I
  haveI : IsScalarTower S S' (LocMod S' N M' I) :=
    ⟨fun a b y => by rw [Algebra.smul_def]; exact mul_smul (algebraMap S S' a) b y⟩
  let g : LocMod S N M I →ₗ[S] LocMod S' N M' I :=
    { gLoc f hX I with map_smul' := gLoc_smul f hX I }
  LinearEquiv.ofBijective (LinearMap.liftBaseChange S' g)
    (bij_of_tmul f hX hf I (LinearMap.liftBaseChange S' g).toAddMonoidHom (fun _ _ => rfl))

end Loc

end FlatBC

namespace FlatBC

section Grade

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c)

end Grade

end FlatBC

namespace FlatBC

section Final

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S'] [Module.Flat S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c) (c : ℤ)

end Final

end FlatBC

end

end GroundTheory.Heights₂.Heights.Kleiman

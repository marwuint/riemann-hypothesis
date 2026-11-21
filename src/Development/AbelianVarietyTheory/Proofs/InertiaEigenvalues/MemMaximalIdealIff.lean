import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic

noncomputable section

namespace GlobalTheory.TripleAdm

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual

section Algebra

variable {g : ℕ} [Fact g.Prime]

theorem nodup_rootsBar {f : (ZMod g)[X]} (hf : Squarefree f) : (rootsBar f).Nodup :=
  nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))

theorem exists_dvd_of_stable {K : Type} [Field K] {N : ℕ} {f : (ZMod g)[X]} (hf : Squarefree f) (a : Fbar g →* K)
    (ha : ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f, a x = a y → x = y) (T P : GL (Fin N) K) (hP : P * T * P⁻¹ = T ^ g)
    (hT : (T : Matrix (Fin N) (Fin N) K).charpoly = ((rootsBar f).map fun x => X - C (a x)).prod)
    (W : Submodule K (Fin N → K)) (hTW : ∀ x ∈ W, (T : Matrix (Fin N) (Fin N) K).mulVec x ∈ W)
    (hPW : ∀ x ∈ W, ((P⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec x ∈ W) :
    ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = Module.finrank K W := by
  classical
  let t : Module.End K (Fin N → K) := Matrix.toLin' (T : Matrix (Fin N) (Fin N) K)
  have ht : ∀ x ∈ W, t x ∈ W := hTW
  set p := LinearMap.charpoly (t.restrict ht) with hp
  have hT' : (T : Matrix (Fin N) (Fin N) K).charpoly = (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [hT, Multiset.map_map]; rfl
  have hdvd : p ∣ (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [← hT', ← Matrix.charpoly_toLin', GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W t ht]
    exact dvd_mul_right _ _
  have h0 : (((rootsBar f).map a).map fun x => X - C x).prod ≠ 0 := hT' ▸ (Matrix.charpoly_monic _).ne_zero
  have hle : p.roots ≤ (rootsBar f).map a := by
    have := roots.le_of_dvd h0 hdvd
    rwa [roots_multiset_prod_X_sub_C] at this
  have hcard : p.roots.card = Module.finrank K W := by
    rw [← LinearMap.charpoly_natDegree (t.restrict ht)]
    refine (Splits.natDegree_eq_card_roots ?_).symm
    exact Splits.of_dvd (Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _) h0 hdvd
  have hnd := nodup_rootsBar hf
  let S := (rootsBar f).filter fun x => a x ∈ p.roots
  have hS : S.map a = p.roots := by
    have h1 : ((rootsBar f).map a).Nodup := hnd.map_on ha
    rw [Multiset.Nodup.ext (Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) h1)
      (Multiset.nodup_of_le hle h1)]
    intro z
    rw [Multiset.mem_map]
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact (Multiset.mem_filter.1 hx).2
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hle hz)
      exact ⟨x, Multiset.mem_filter.2 ⟨hx, hz⟩, rfl⟩
  have hroot : ∀ c, c ∈ p.roots ↔ ∃ w ∈ W, w ≠ 0 ∧ (T : Matrix (Fin N) (Fin N) K).mulVec w = c • w := fun c => by
    rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := h.exists_hasEigenvector
      exact ⟨w.1, w.2, fun h => hw.2 (Subtype.ext h), congrArg Subtype.val hw.apply_eq_smul⟩
    · rintro ⟨w, hw, h1, h2⟩
      exact Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩)
        ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext h2), fun h => h1 (congrArg Subtype.val h)⟩
  have hst : ∀ x ∈ S, x ^ g ∈ S := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.1 hx
    refine Multiset.mem_filter.2 ⟨rootsBar_frob f ▸ Multiset.mem_map_of_mem _ hx1, ?_⟩
    obtain ⟨w, hw, h1, h2⟩ := (hroot _).1 hx2
    have h3 : ∀ n : ℕ, ((T ^ n : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec w = a x ^ n • w := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ']
    refine (hroot _).2 ⟨_, hPW w hw, fun h => h1 ?_, ?_⟩
    · rw [← Matrix.one_mulVec w, ← Units.val_one, ← mul_inv_cancel P, Units.val_mul, ← Matrix.mulVec_mulVec, h,
        Matrix.mulVec_zero]
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, show T * P⁻¹ = P⁻¹ * T ^ g by rw [← hP]; group, Units.val_mul,
        ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, map_pow]
  have hSn : S.Nodup := hnd.filter _
  obtain ⟨q, hq, hqS⟩ := GlobalTheory.Compare.TeichmullerRoots.exists_monic_of_stable S (by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (hSn.map (frobenius (Fbar g) g).injective)).2 ?_)
      (Multiset.card_map _ _).ge
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    exact hst x hx)
  refine ⟨q, ?_, by rw [← card_rootsBar, hqS, ← hcard, ← hS, Multiset.card_map]⟩
  rw [← map_dvd_map' (algebraMap (ZMod g) (Fbar g))]
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (hq.map _).ne_zero ?_
  exact hqS.trans_le (Multiset.filter_le _ _)

theorem irredOn_of_labels {l N : ℕ} [Fact l.Prime] {PP Γ : Type} [Group Γ] {f : PP → (ZMod g)[X]}
    (hd : ∀ v, (f v).natDegree = N) (hf : ∀ v, Squarefree (f v))
    (h4 : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a)
    (a : PP → Fbar g →* Fbar l) (ha : ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v), a v x = a v y → x = y)
    (ρ : Γ →* GL (Fin N) (Fbar l)) (τ : PP → Γ) (hφ : ∀ v, ∃ φ, ρ (φ * τ v * φ⁻¹) = ρ (τ v) ^ g)
    (hτ : ∀ v, ((ρ (τ v) : GL (Fin N) (Fbar l)) : Matrix (Fin N) (Fin N) (Fbar l)).charpoly =
      ((rootsBar (f v)).map fun x => X - C (a v x)).prod) : IrredOn ρ ⊤ := by
  intro W hW
  have key : ∀ v, ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = Module.finrank (Fbar l) W := fun v => by
    obtain ⟨φ, h⟩ := hφ v
    rw [map_mul, map_mul, map_inv] at h
    exact exists_dvd_of_stable (hf v) (a v) (ha v) _ _ h (hτ v) W (hW _ trivial)
      (by rw [← map_inv]; exact hW _ trivial)
  have hle : Module.finrank (Fbar l) W ≤ N := by simpa using W.finrank_le
  by_contra hc
  rw [not_or] at hc
  have h0 : Module.finrank (Fbar l) W ≠ 0 := fun h => hc.1 (Submodule.finrank_eq_zero.1 h)
  have h1 : Module.finrank (Fbar l) W ≠ N := fun h => hc.2 (Submodule.eq_top_of_finrank_eq (by simpa using h))
  by_cases h : 2 * Module.finrank (Fbar l) W ≤ N
  · obtain ⟨v, hv⟩ := h4 _ (by omega) h
    exact hv (key v)
  · obtain ⟨v, hv⟩ := h4 (N - Module.finrank (Fbar l) W) (by omega) (by omega)
    obtain ⟨q, ⟨q', hq⟩, hqa⟩ := key v
    have hne : q * q' ≠ 0 := hq ▸ (hf v).ne_zero
    have hdeg := hd v
    rw [hq, natDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at hdeg
    exact hv ⟨q', Dvd.intro_left _ hq.symm, by omega⟩

theorem primeToPart_eq_of_eq {l : ℕ} [Fact l.Prime] (a : Fbar g →* Fbar l)
    (ha : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → a x = a y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0) (h : a x = a y) : primeToPart l x = primeToPart l y := by
  have key : ∀ x : Fbar g, x ≠ 0 → primeToPart l x ≠ 0 ∧ (orderOf (primeToPart l x)).Coprime l := fun x hx => by
    obtain ⟨-, M, -, h1, h2, -⟩ := GlobalTheory.TameRed.part_spec (Fact.out : l.Prime) (isOfFinOrder_of_ne_zero hx)
    exact ⟨pow_ne_zero _ hx, h1.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)⟩
  refine ha _ _ (key x hx).1 (key y hy).1 (key x hx).2 (key y hy).2 ?_
  rw [GlobalTheory.TypeLeaf.map_primeToPart_fbar, GlobalTheory.TypeLeaf.map_primeToPart_fbar, h]

theorem charpoly_smul_congr {K : Type} [Field K] [Infinite K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (c : Kˣ)
    (h : A.charpoly = B.charpoly) : ((c : K) • A).charpoly = ((c : K) • B).charpoly := by
  have e : ∀ (M : Matrix (Fin n) (Fin n) K) (z : K), Matrix.scalar (Fin n) z - (c : K) • M =
      (c : K) • (Matrix.scalar (Fin n) (z / c) - M) := fun M z => by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    funext x
    simp [mul_div_cancel₀ _ c.ne_zero]
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, e, e, Matrix.det_smul, Matrix.det_smul, ← Matrix.eval_charpoly,
    ← Matrix.eval_charpoly, h]

end Algebra

open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host

variable {D : D7}

section Row

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}

theorem root_ne_zero (hg : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k) {x : Fb (D.host.g k) (D.host.g_prime k)}
    (hx : x ∈ @rootsBar _ ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)) : x ≠ 0 := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rintro rfl
  exact ((hg k).1.1 v).2.2 ((GlobalTheory.Compare.TeichmullerRoots.zero_mem_rootsBar ((hg k).1.1 v).1).1 hx)

theorem toFb_ne_zero (k : Fin 2) (u : (ZMod (D.host.g k))ˣ) : toFb D k u ≠ 0 :=
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  (map_ne_zero_iff _ (algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k))).injective).2 u.ne_zero

end Row

section Comparison₂

variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}

theorem norm_toQ_le (ρ : Reading Y i b) (x : Y.O0 i) : ‖toQ ρ.κ x‖ ≤ 1 := by
  have h : IsIntegral ℤ_[Y.l i] x := Algebra.IsIntegral.isIntegral x
  let f : Y.O0 i →ₐ[ℤ_[Y.l i]] Qbar (Y.l i) := { toQ ρ.κ with commutes' := ρ.κ_alg }
  obtain ⟨p, hp, h0⟩ : IsIntegral ℤ_[Y.l i] (toQ ρ.κ x) := h.map f
  let v := NormedField.valuation (K := Qbar (Y.l i))
  let z : ℤ_[Y.l i] →+* v.integer := (algebraMap ℤ_[Y.l i] (Qbar (Y.l i))).codRestrict _ fun a => by
    change ‖algebraMap ℚ_[Y.l i] (Qbar (Y.l i)) (a : ℚ_[Y.l i])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  exact (Valuation.integer.integers v).mem_of_integral ⟨p.map z, hp.map z, by rw [eval₂_map]; exact h0⟩

def toZ (ρ : Reading Y i b) : Y.O0 i →+* Zbar (Y.l i) := (toQ ρ.κ).codRestrict _ (norm_toQ_le ρ)

theorem mem_maximalIdeal_iff (ρ : Reading Y i b) (x : Y.O0 i) :
    x ∈ IsLocalRing.maximalIdeal (Y.O0 i) ↔ ‖toQ ρ.κ x‖ < 1 := by
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← not_le, not_iff_not]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨u, rfl⟩
    have h1 : ‖toQ ρ.κ u‖ * ‖toQ ρ.κ (u⁻¹ : (Y.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    nlinarith [norm_toQ_le ρ (u⁻¹ : (Y.O0 i)ˣ), norm_nonneg (toQ ρ.κ u)]
  · have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, norm_zero] at h
      exact absurd h (by norm_num)
    obtain ⟨y, hy⟩ := hint (algebraMap (Y.O0 i) (FractionRing (Y.O0 i)) x)⁻¹ (by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ h)
    refine IsUnit.of_mul_eq_one y (IsFractionRing.injective _ (FractionRing (Y.O0 i)) ?_)
    rw [map_mul, hy, map_one, mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0)]

theorem exists_residue_lift (ρ : Reading Y i b) {K : Type} [Field K] (f : Y.O0 i →+* K) (hl : ((Y.l i : ℕ) : K) = 0) :
    ∃ κ : IsLocalRing.ResidueField (Y.O0 i) →+* K, ∀ x, κ (IsLocalRing.residue _ x) = f x := by
  have h0 : RingHom.ker f ≠ ⊥ := fun h => by
    have h1 : ((Y.l i : ℕ) : Y.O0 i) ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_natCast, hl]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (toQ ρ.κ) h1
    rw [map_natCast, map_zero] at h2
    exact (Y.lPrime i).out.ne_zero (by exact_mod_cast h2)
  have h1 := IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime f).isMaximal h0)
  exact ⟨Ideal.Quotient.lift _ f fun x hx => by rwa [← h1] at hx, fun _ => rfl⟩

variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem antiHom_of_isLAdicOf (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar D.host.E} {n : (D.host.E →+* ℂ) → ℤ} {r : GalE D →* (Qbar l)ˣ} (hc : Continuous r)
    (h : GlobalTheory.HeckeGal.IsLAdicOf art ι χ n r) (ht : χ.TrivOn D.host.F) : AntiHom Y.cc r := by
  obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have h1 : ∀ x : D.host.E, Y.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
    obtain ⟨j, hj⟩ := Y.cc_cm.1
    apply j.injective
    rw [hj, hc1]
    exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  exact GlobalTheory.AntiLAdic.antiHom_of_trivOn D.host.F D.host.E c hcm.rank hcm.ne (fun x => by rw [hc1, hc1, conj_conj]) hr
    D.nd.Om Y.cc h1 art ha l ι χ n _ hc h ht

variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}

end Comparison₂

end GlobalTheory.TripleAdm

end

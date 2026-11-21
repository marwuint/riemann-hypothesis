import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepAtlas

section Lin

variable {R R' N N' : Type} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R' N']
  {m k r : ℕ}

theorem initSpan_top (u : Fin m → N) : initSpan R u m = Submodule.span R (Set.range u) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

theorem not_mem_initSpan [Nontrivial R] {u : Fin m → N} (hu : LinearIndependent R u) (i : Fin m) :
    u i ∉ initSpan R u i := hu.notMem_span_image (lt_irrefl (i : ℕ))

theorem initSpan_succ_le {u : Fin m → N} {W : Submodule R N} (i : Fin m) (h : initSpan R u i ≤ W) (hi : u i ∈ W) :
    initSpan R u (i + 1) ≤ W := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | h'
  · exact h (Submodule.subset_span ⟨j, h', rfl⟩)
  · rwa [Fin.ext h']

theorem mem_initSpan_inl {n : ℕ} (b : Module.Basis (Fin k ⊕ Fin n) R N) (v : N) :
    v ∈ initSpan R (fun i : Fin k => b (.inl i)) k ↔ ∀ j, b.repr v (.inr j) = 0 := by
  rw [initSpan_top, show Set.range (fun i : Fin k => b (.inl i)) = b '' Set.range Sum.inl from by
    rw [← Set.range_comp]; rfl, b.mem_span_image]
  refine ⟨fun h j => ?_, fun h => ?_⟩
  · by_contra h'
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 h')
    cases hi
  · rintro (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)

end Lin

section Carry

variable {Z Z' : Scheme.{0}} {C : Coc Z} {f : Z' ⟶ Z} {L : C.Line f} {S : Type} [CommRing S] {w : Sp S ⟶ Z'}

theorem carries_smul {α : C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α} {ξ : Fin (C.n α) → S} (hξ : L.Carries w α h ξ) (s : Sˣ) :
    L.Carries w α h ((s : S) • ξ) := fun β hw => by
  obtain ⟨u, hu⟩ := hξ β hw
  refine ⟨s * u, ?_⟩
  rw [Matrix.mulVec_smul, hu]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_assoc]

theorem exists_chart [IsLocalRing S] (L : C.Line f) (w : Sp S ⟶ Z') : ∃ β, ⊤ ≤ w ⁻¹ᵁ L.B β :=
  FlagMod.exists_chart_of_isLocalRing (eq_top_iff.2 fun x _ => by
    obtain ⟨β, hβ⟩ := L.cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨β, hβ⟩) w

end Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}
  {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ} {K : Type} [Field K]

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crd_eq {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crd b z h v = crdL b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u))
    (α : D.C.A) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, mem_initSpan_inl]
  exact funext_iff

theorem linearIndependent_of_flagAt {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (τ : E →+* ℂ) :
    LinearIndependent K (u τ) := by
  obtain ⟨a, φ, -, hf, -⟩ := hu
  exact ((isFrame_up_iff _ _).1 hf τ).1

def Good (D : Adapted A σ k) (hk : k < Dw.mult σ) {X' : Scheme.{0}} {f : X' ⟶ X} (L : D.C.Line f) (w : Sp K ⟶ X')
    (u : TVecs Dw M.t ((w ≫ f) ≫ π)) : Prop :=
  A.FlagAt (w ≫ f) (up u) ∧ ∀ α h, L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))

variable {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f} {w : Sp K ⟶ X'}
  {u u' : TVecs Dw M.t ((w ≫ f) ≫ π)} {ty' : (E →+* ℂ) → Finset ℕ}

theorem Good.le (h : Good D hk L w u) (h' : Good D hk L w u') (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j := by
  intro τ j hj
  by_cases hτ : τ = σ
  swap
  · exact (h'.1.initSpan_eq h.1 τ (h2 τ hτ ▸ hj)).le
  subst hτ
  rw [h1, Finset.mem_insert] at hj
  rcases hj with rfl | hj
  swap
  · exact (h'.1.initSpan_eq h.1 τ hj).le
  obtain ⟨β, hβ⟩ := exists_chart L w
  have hα := le_preimage_map f (L.le β) hβ
  obtain ⟨s, hs⟩ := h.2 _ hα β hβ
  obtain ⟨s', hs'⟩ := h'.2 _ hα β hβ
  rw [Coc.tr_self, Matrix.one_mulVec, crd_eq] at hs hs'
  have hle := FlagMod.initSpan_mono (R := K) (u τ) (Nat.le_succ k)
  refine initSpan_succ_le ⟨k, hk⟩ (fun v hv => hle ?_) ?_
  · exact (crdL_eq_zero_iff D h.1 _ hα v).1 ((crdL_eq_zero_iff D h'.1 _ hα v).2 hv)
  · have : u' τ ⟨k, hk⟩ - ((s' * s⁻¹ : Kˣ) : K) • u τ ⟨k, hk⟩ ∈ initSpan K (u τ) k := by
      rw [← crdL_eq_zero_iff D h.1 _ hα, map_sub, map_smul, hs, hs']
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, Pi.zero_apply, mul_assoc,
        Units.inv_mul_cancel_left, sub_self]
    have h3 : u τ ⟨k, hk⟩ ∈ initSpan K (u τ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
    simpa using Submodule.add_mem _ (hle this) (Submodule.smul_mem _ ((s' * s⁻¹ : Kˣ) : K) h3)

theorem Good.of_le (h : Good D hk L w u) {a : A.ch.ι} {φ : A.ch.R a →+* K} (e : spMap φ ≫ A.ch.χ a = w ≫ f)
    (hf : LocM.IsFrame M.t (φ.comp (A.alg a)) ((w ≫ f) ≫ π) (up u')) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (hle : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j) :
    Good D hk L w u' := by
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have hsub : ∀ τ, ∀ j ∈ ty τ, j ∈ ty' τ := fun τ j hj => by
    by_cases hτ : τ = σ
    · subst hτ
      rw [h1]
      exact Finset.mem_insert_of_mem hj
    · rwa [h2 τ hτ]
  have hi := linearIndependent_of_flagAt h.1
  have hF : A.FlagAt (w ≫ f) (up u') := (A.flagAt_iff e h₀ u').2 ⟨hf, fun τ j hj =>
    (initSpan_eq_of_le (hi τ) ((isFrame_up_iff _ _).1 hf τ).1 (hle τ j (hsub τ j hj))).trans
      (((A.flagAt_iff e h₀ u).1 h.1).2 τ j hj)⟩
  refine ⟨hF, fun α hα => ?_⟩
  have h3 : u' σ ⟨k, hk⟩ ∈ initSpan K (u' σ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
  obtain ⟨s, hs, -⟩ := FlagMod.existsUnique_sub_mem_initSpan (hi σ) ⟨k, hk⟩
    (hle σ (k + 1) (h1 ▸ Finset.mem_insert_self _ _) h3)
  have hs' := (crdL_eq_zero_iff D h.1 α hα _).2 hs
  rw [map_sub, map_smul, sub_eq_zero] at hs'
  have h0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, crdL_eq_zero_iff D hF] at hs'
    exact not_mem_initSpan (linearIndependent_of_flagAt hF σ) ⟨k, hk⟩ hs'
  rw [crd_eq, hs']
  exact carries_smul (h.2 α hα) (Units.mk0 s h0)

end GlobalTheory.DRFlag.StepAtlas

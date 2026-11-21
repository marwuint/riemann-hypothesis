import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan le_preimage_comp)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellAtlas

section Lin

variable {R N N' : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] {m k : ℕ}

theorem initSpan_castLE (hk : k ≤ m) (u : Fin m → N) :
    initSpan R u k = Submodule.span R (Set.range fun i : Fin k => u (Fin.castLE hk i)) := by
  rw [initSpan]
  congr 1
  ext v
  exact ⟨fun ⟨j, hj, e⟩ => ⟨⟨j, hj⟩, e⟩, fun ⟨i, e⟩ => ⟨_, i.2, e⟩⟩

theorem map_initSpan (F : N →ₗ[R] N') (u : Fin m → N) (e : ℕ) :
    (initSpan R u e).map F = initSpan R (fun i => F (u i)) e := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}
  {A : Atlas M π ty} {D : LCrd M π} {σ : E →+* ℂ} {a k b : ℕ} {K : Type} [Field K]

theorem linearIndependent_of_flagAt {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (τ : E →+* ℂ) :
    LinearIndependent K (u τ) := by
  obtain ⟨a, φ, -, hf, -⟩ := hu
  exact ((isFrame_up_iff _ _).1 hf τ).1

theorem range_subset_of_flagAt {z : Sp K ⟶ X} {u : Vecs Dw M.t K} (hu : A.FlagAt z u) :
    Set.range z ⊆ π ⁻¹' Set.range M.j := by
  obtain ⟨a, φ, e, -⟩ := hu
  rw [← A.cover]
  exact A.ch.range_subset e

theorem exists_chart {Z : Scheme.{0}} (C : Coc Z) (z : Sp K ⟶ Z) : ∃ β, ⊤ ≤ z ⁻¹ᵁ C.B β :=
  FlagMod.exists_chart_of_isLocalRing (eq_top_iff.2 fun x _ => by
    obtain ⟨β, hβ⟩ := C.cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨β, hβ⟩) z

variable (D) in

def embL (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) :
    TanM (z ≫ π) M.t.G →ₗ[S] (Fin (D.N + 1) → S) :=
  ((D.Em.A α).map (ev z _ h)).mulVecLin.comp (D.crd α S z h)

theorem emb_congr (α : D.C.A) {z z' : Sp K ⟶ X} (e : z = z') (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (h' : ⊤ ≤ z' ⁻¹ᵁ D.C.B α)
    {U : TVecs Dw M.t (z ≫ π)} {U' : TVecs Dw M.t (z' ≫ π)} (hU : up U = up U') (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    D.emb α z h (U τ i) = D.emb α z' h' (U' τ i) := by
  subst e
  rw [up_injective hU]

variable (D A) in

def Good (hk : k ≤ Dw.mult σ) {X' : Scheme.{0}} (f : X' ⟶ X) (q : X' ⟶ PSpace V (plN D.N k)) (w : Sp K ⟶ X')
    (u : TVecs Dw M.t ((w ≫ f) ≫ π)) : Prop :=
  A.FlagAt (w ≫ f) (up u) ∧
    ∀ α h, Car D.Em f q w α h fun i => D.crd α K (w ≫ f) h (u σ (Fin.castLE hk i))

variable {hk : k ≤ Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {q : X' ⟶ PSpace V (plN D.N k)} {w : Sp K ⟶ X'}
  {u u' : TVecs Dw M.t ((w ≫ f) ≫ π)} {ty' : (E →+* ℂ) → Finset ℕ}

theorem Good.initSpan_eq (h : Good A D hk f q w u) (h' : Good A D hk f q w u') :
    initSpan K (u' σ) k = initSpan K (u σ) k := by
  obtain ⟨α, hα⟩ := exists_chart D.C (w ≫ f)
  have h1 := (((car_span _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.2 α hα)).2.1 _).1 (h'.2 α hα)).2
  refine Submodule.map_injective_of_injective (D.inj α K _ hα (range_subset_of_flagAt h.1)) ?_
  rw [map_initSpan, map_initSpan, initSpan_castLE hk, initSpan_castLE hk]
  exact h1

theorem Good.of_initSpan_eq (h : Good A D hk f q w u) (hu : A.FlagAt (w ≫ f) (up u'))
    (e : initSpan K (u' σ) k = initSpan K (u σ) k) : Good A D hk f q w u' := by
  refine ⟨hu, fun α hα => ((car_span _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.2 α hα)).2.1 _).2 ⟨?_, ?_⟩⟩
  · exact ((linearIndependent_of_flagAt hu σ).comp _ (Fin.castLE_injective hk)).map' _
      (LinearMap.ker_eq_bot.2 (D.inj α K _ hα (range_subset_of_flagAt hu)))
  · have := congrArg (Submodule.map (D.crd α K (w ≫ f) hα)) e
    rwa [map_initSpan, map_initSpan, initSpan_castLE hk, initSpan_castLE hk] at this

theorem Good.le (h : Good A D hk f q w u) (h' : Good A D hk f q w u') (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j := by
  intro τ j hj
  by_cases hτ : τ = σ
  swap
  · exact (h'.1.initSpan_eq h.1 τ (h2 τ hτ ▸ hj)).le
  subst hτ
  rw [h1, Finset.mem_insert] at hj
  rcases hj with rfl | hj
  · exact (h.initSpan_eq h').le
  · exact (h'.1.initSpan_eq h.1 τ hj).le

theorem Good.of_le (h : Good A D hk f q w u) {j : A.ch.ι} {φ : A.ch.R j →+* K} (e : spMap φ ≫ A.ch.χ j = w ≫ f)
    (hf : LocM.IsFrame M.t (φ.comp (A.alg j)) ((w ≫ f) ≫ π) (up u')) (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (hle : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j) :
    Good A D hk f q w u' := by
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
  exact h.of_initSpan_eq hF (initSpan_eq_of_le (hi σ) ((isFrame_up_iff _ _).1 hf σ).1
    (hle σ k (h1 ▸ Finset.mem_insert_self _ _)))

theorem Good.comp_eq (ho : q ≫ PSpace.str V _ = f ≫ π ≫ M.s) (h : Good A D hk f q w u) {w' : Sp K ⟶ X'}
    {U' : TVecs Dw M.t ((w' ≫ f) ≫ π)} (h' : Good A D hk f q w' U') (e : w ≫ f = w' ≫ f) (hU : up u = up U') :
    w ≫ q = w' ≫ q := by
  obtain ⟨α, hα⟩ := exists_chart D.C (w ≫ f)
  have hα' : ⊤ ≤ (w' ≫ f) ⁻¹ᵁ D.C.B α := e ▸ hα
  obtain ⟨g, hv, h1⟩ := h.2 α hα
  obtain ⟨g', hv', h1'⟩ := h'.2 α hα'
  have hg : g = g' := by
    have h3 : spMap g = spMap g' := by
      rw [← ProjSpace.pt_str g _ hv, ← ProjSpace.pt_str g' _ hv', ← h1, ← h1', Category.assoc, Category.assoc, ho,
        ← Category.assoc, e, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
  subst hg
  rw [h1, h1']
  congr 2
  funext i
  exact emb_congr α e hα hα' hU σ _

end GlobalTheory.GrCl.CellAtlas

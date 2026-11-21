import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

namespace GlobalTheory.LocM.MapComp

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k N N' : Type} [Field k] [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N'] {m : ℕ}

def IsBas (M : Submodule k N) (b : Fin m → N) : Prop :=
  (∀ i, b i ∈ M) ∧ ∀ n ∈ M, ∃! a : Fin m → k, n = ∑ j, a j • b j

theorem isBas_iff (M : Submodule k N) (b : Fin m → N) :
    IsBas M b ↔ Function.Injective (Fintype.linearCombination k b) ∧
      LinearMap.range (Fintype.linearCombination k b) = M := by
  constructor
  · rintro ⟨h1, h2⟩
    have hm : ∀ a : Fin m → k, ∑ j, a j • b j ∈ M := fun a =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i)
    refine ⟨fun a a' h => (h2 _ (hm a)).unique rfl h, le_antisymm ?_ fun n hn => ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact hm a
    · obtain ⟨a, ha, -⟩ := h2 n hn
      exact ⟨a, ha.symm⟩
  · rintro ⟨h1, rfl⟩
    refine ⟨fun i => ⟨Pi.single i 1, by simp⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl, fun a' h => (h1 h).symm⟩

theorem IsBas.transfer {M : Submodule k N} {M' : Submodule k N'} {b b' : Fin m → N} {c : Fin m → N'}
    (A : Fin m → Fin m → k) (hb' : IsBas M b') (hA : ∀ i, b' i = ∑ j, A i j • b j) (hc : IsBas M' c) :
    IsBas M' fun i => ∑ j, A i j • c j := by
  let L : (Fin m → k) →ₗ[k] (Fin m → k) := Fintype.linearCombination k A
  have key : ∀ {P : Type} [AddCommGroup P] [Module k P] (d : Fin m → P),
      Fintype.linearCombination k (fun i => ∑ j, A i j • d j) = Fintype.linearCombination k d ∘ₗ L := by
    intro P _ _ d
    refine LinearMap.ext fun a => ?_
    simp only [L, LinearMap.comp_apply, Fintype.linearCombination_apply, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  obtain rfl : b' = fun i => ∑ j, A i j • b j := funext hA
  rw [isBas_iff, key] at hb' ⊢
  rw [isBas_iff] at hc
  have hL : Function.Injective L := Function.Injective.of_comp (f := Fintype.linearCombination k b) hb'.1
  have hS : Function.Surjective L := LinearMap.surjective_of_injective hL
  exact ⟨hc.1.comp hL, by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hS), hc.2]⟩

def head (r : ℕ) (d : Fin m → N) : Submodule k N :=
  Submodule.span k (Set.range fun j : {j : Fin m // (j : ℕ) < r} => d j)

theorem mem_head {r : ℕ} {d : Fin m → N} {w : N} :
    w ∈ (head r d : Submodule k N) ↔ ∃ cf : Fin m → k, (∀ j : Fin m, r ≤ (j : ℕ) → cf j = 0) ∧ w = ∑ j, cf j • d j := by
  classical
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 h
    refine ⟨fun j => if h : (j : ℕ) < r then a ⟨j, h⟩ else 0, fun j hj => dif_neg (not_lt.2 hj), ?_⟩
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin m => (j : ℕ) < r)]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun j : {j : Fin m // ¬ (j : ℕ) < r} => _)
      (fun j _ => by simp only [dif_neg j.2, zero_smul]), add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp only [dif_pos j.2]
  · rintro ⟨cf, h0, rfl⟩
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < r
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rw [h0 j (not_lt.1 hj), zero_smul]
      exact zero_mem _

theorem head_le_iff {r : ℕ} {d d' : Fin m → N} :
    (head r d' : Submodule k N) ≤ head r d ↔ ∀ i : Fin m, (i : ℕ) < r → d' i ∈ (head r d : Submodule k N) := by
  rw [head, Submodule.span_le, Set.range_subset_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

theorem head_ge {M : Submodule k N} {r : ℕ} {d b : Fin m → N} (hb : IsBas M b)
    (h : (head r b : Submodule k N) ≤ head r d) : (head r d : Submodule k N) ≤ head r b := by
  have hl : LinearIndependent k b := Fintype.linearIndependent_iff.2 fun g hg =>
    congrFun (((isBas_iff M b).1 hb).1 (a₁ := g) (a₂ := 0) (hg.trans (map_zero _).symm))
  have hl' : LinearIndependent k fun j : {j : Fin m // (j : ℕ) < r} => b j := hl.comp _ Subtype.val_injective
  have : FiniteDimensional k (head r d : Submodule k N) := FiniteDimensional.span_of_finite k (Set.finite_range _)
  refine (Submodule.eq_of_le_of_finrank_le h ?_).ge
  exact (finrank_range_le_card (R := k) _).trans (finrank_span_eq_card hl').ge

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') :
    w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  obtain rfl : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rfl

theorem comb_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {S : Type} [CommRing S] {x : Sp S ⟶ X'} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)} {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t'.G.left}
    (h : IsCombAtG t' x v a w) : IsCombAtG t (x ≫ τ) (fun i => v i ≫ mu.φ) a (w ≫ mu.φ) := by
  obtain ⟨u, hu, rfl⟩ := h
  let U : tEpsG (x ≫ τ) ⟶ Over.mk ((tEpsG x).hom ≫ τ) := Over.homMk (𝟙 _) (by simp)
  let P : (tEpsG x ⟶ t'.G) →* (tEpsG (x ≫ τ) ⟶ t.G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U).comp (pushHom mu.cart (tEpsG x))
  have hP : ∀ z, (P z).left = z.left ≫ mu.φ := fun z => Category.id_comp _
  refine ⟨fun i => P (u i), fun i => by rw [hP, hu, Category.assoc], ?_⟩
  rw [← hP, map_list_prod, List.map_ofFn]
  rfl

theorem sameFlag_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {S : Type} [CommRing S] {x : Sp S ⟶ X'}
    {ty ty' : (E →+* ℂ) → Finset ℕ} (hty : ∀ σ, ty σ ⊆ ty' σ) {u v : Vecs Dw t' S} (h : SameFlag ty' t' x u v) :
    SameFlag ty t (x ≫ τ) (Dw := Dw) (fun σ i => u σ i ≫ mu.φ) (fun σ i => v σ i ≫ mu.φ) := fun σ r hr i hi => by
  obtain ⟨cf, h0, hc⟩ := h σ r (hty σ hr) i hi
  exact ⟨cf, h0, comb_push mu hc⟩

variable {k : Type} [Field k] {x : Sp k ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem exists_coord (hx : IsUnivChart _ n xc) (u : Vecs Dw t k) (hu : ∀ σ i, IsTanAtG t x (u σ i)) :
    ∃ b : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k, u = fun σ i => vec t x xc (b σ i) := by
  choose b hb using fun σ i => vec_exists hx (u σ i) (hu σ i)
  exact ⟨b, funext fun σ => funext fun i => hb σ i⟩

theorem isFrame_iff (hx : IsUnivChart _ n xc) {l : Level H} {c : Coeff l} (f : c.F →+* k)
    (b : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k) :
    IsFrame t f x (Dw := Dw) (fun σ i => vec t x xc (b σ i)) ↔ ∀ σ, IsBas (eig c f hx σ) (b σ) := by
  constructor
  · rintro ⟨h1, h2⟩ σ
    refine ⟨fun i => (vec_eig_iff hx _ _).1 (h1 σ i).2, fun cc hc => ?_⟩
    simpa only [comb_iff hx] using h2 σ _ (vec_tan hx cc) ((vec_eig_iff hx _ _).2 hc)
  · intro h
    refine ⟨fun σ i => ⟨vec_tan hx _, (vec_eig_iff hx _ _).2 ((h σ).1 i)⟩, fun σ w hw he => ?_⟩
    obtain ⟨cc, rfl⟩ := vec_exists hx w hw
    simpa only [comb_iff hx] using (h σ).2 cc ((vec_eig_iff hx _ _).1 he)

theorem sameFlag_iff (hx : IsUnivChart _ n xc) (ty : (E →+* ℂ) → Finset ℕ)
    (b b' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k) :
    SameFlag ty t x (Dw := Dw) (fun σ i => vec t x xc (b σ i)) (fun σ i => vec t x xc (b' σ i)) ↔
      ∀ σ, ∀ r ∈ ty σ, (head r (b' σ) : Submodule k _) ≤ head r (b σ) := by
  simp only [SameFlag, head_le_iff, mem_head, comb_iff hx]

theorem sameFlag_trans {ty : (E →+* ℂ) → Finset ℕ} {u v w : Vecs Dw t k} (hu : ∀ σ i, IsTanAtG t x (u σ i))
    (hv : ∀ σ i, IsTanAtG t x (v σ i)) (hw : ∀ σ i, IsTanAtG t x (w σ i)) (h : SameFlag ty t x u v)
    (h' : SameFlag ty t x v w) : SameFlag ty t x u w := by
  obtain ⟨n, xc, hx⟩ := exists_chart t x
  obtain ⟨a, rfl⟩ := exists_coord hx u hu
  obtain ⟨b, rfl⟩ := exists_coord hx v hv
  obtain ⟨c, rfl⟩ := exists_coord hx w hw
  rw [sameFlag_iff hx] at h h' ⊢
  exact fun σ r hr => (h' σ r hr).trans (h σ r hr)

theorem sameFlag_symm {ty : (E →+* ℂ) → Finset ℕ} {l : Level H} {c : Coeff l} {f : c.F →+* k} {u v : Vecs Dw t k}
    (hu : ∀ σ i, IsTanAtG t x (u σ i)) (hv : IsFrame t f x v) (h : SameFlag ty t x u v) : SameFlag ty t x v u := by
  obtain ⟨n, xc, hx⟩ := exists_chart t x
  obtain ⟨a, rfl⟩ := exists_coord hx u hu
  obtain ⟨b, rfl⟩ := exists_coord hx v fun σ i => (hv.1 σ i).1
  rw [sameFlag_iff hx] at h ⊢
  rw [isFrame_iff hx] at hv
  exact fun σ r hr => head_ge (hv σ) (h σ r hr)

theorem isFrame_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {x' : Sp k ⟶ X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}
    {f : c.F →+* k} {f' : c'.F →+* k} {u v : Vecs Dw t' k} (hu : IsFrame t' f' x' u) (hv : IsFrame t' f' x' v)
    (h : IsFrame t f (x' ≫ τ) (Dw := Dw) fun σ i => u σ i ≫ mu.φ) :
    IsFrame t f (x' ≫ τ) (Dw := Dw) fun σ i => v σ i ≫ mu.φ := by
  choose A hA using fun σ i => (hu.2 σ (v σ i) (hv.1 σ i).1 (hv.1 σ i).2).exists
  have hA' := fun σ i => comb_push mu (hA σ i)
  obtain ⟨n, xc, hx⟩ := exists_chart t (x' ≫ τ)
  obtain ⟨n', xc', hx'⟩ := exists_chart t' x'
  obtain ⟨d, hd⟩ := exists_coord hx _ fun σ i => (h.1 σ i).1
  obtain ⟨a, rfl⟩ := exists_coord hx' u fun σ i => (hu.1 σ i).1
  obtain ⟨b, rfl⟩ := exists_coord hx' v fun σ i => (hv.1 σ i).1
  rw [hd, isFrame_iff hx] at h
  rw [isFrame_iff hx'] at hv
  have e : (fun σ i => vec t' x' xc' (b σ i) ≫ mu.φ : Vecs Dw t k) =
      fun σ i => vec t (x' ≫ τ) xc (∑ j, A σ i j • d σ j) := funext fun σ => funext fun i => by
    refine comb_unique (hA' σ i) ?_
    rw [show (fun j => vec t' x' xc' (a σ j) ≫ mu.φ) = fun j => vec t (x' ≫ τ) xc (d σ j) from congrFun hd σ]
    exact (comb_iff hx _ _ _).2 rfl
  rw [e, isFrame_iff hx]
  exact fun σ => IsBas.transfer (A σ) (hv σ) (fun i => (comb_iff hx' _ _ _).1 (hA σ i)) (h σ)

end Tan

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem ringHom_ext_valuationSubring {F k : Type} [Field F] [Field k] (V : ValuationSubring F) {f g : F →+* k}
    (h : f.comp V.subtype = g.comp V.subtype) : f = g := RingHom.ext fun x => by
  rcases V.mem_or_inv_mem x with hx | hx
  · exact RingHom.congr_fun h ⟨x, hx⟩
  · have : f x⁻¹ = g x⁻¹ := RingHom.congr_fun h ⟨x⁻¹, hx⟩
    rwa [map_inv₀, map_inv₀, inv_inj] at this

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem tan_chart (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* k}
    (h : spMap φ ≫ Z.chart a = w) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    IsTanAtG (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ σ j) := by
  rw [← h, Category.assoc]
  exact GlobalTheory.FactorDepth.isTanAtG_map _ φ ((Z.frame a).1 σ j).1

theorem flagAt_two (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {u v : Vecs Dw (Y Z.i).t k}
    (hu : Z.FlagAt w u) (hv : Z.FlagAt w v) : ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (w ≫ Z.π) u ∧
      IsFrame (Y Z.i).t f (w ≫ Z.π) v ∧ SameFlag Z.ty (Y Z.i).t (w ≫ Z.π) u v := by
  obtain ⟨a, φ, ha, fu, su⟩ := hu
  obtain ⟨b, ψ, hb, fv, sv⟩ := hv
  have e : φ.comp (Z.alg a) = ψ.comp (Z.alg b) := ringHom_ext_valuationSubring (Z.i.c.V W) (spMap_inj (by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← sp_comp _ φ, ← sp_comp _ ψ, ← Z.alg_s, ← Z.alg_s, ← Category.assoc,
      ← Category.assoc, ha, hb]))
  have g := Z.glue k a b φ ψ (ha.trans hb.symm)
  rw [← Category.assoc, ha] at g
  refine ⟨_, fu, e ▸ fv, ?_⟩
  exact sameFlag_trans (fun σ j => (fu.1 σ j).1) (tan_chart Z ha) (fun σ j => (fv.1 σ j).1)
    (sameFlag_symm (tan_chart Z ha) fu su)
    (sameFlag_trans (tan_chart Z ha) (tan_chart Z hb) (fun σ j => (fv.1 σ j).1) g sv)

end GlobalTheory.LocM.MapComp

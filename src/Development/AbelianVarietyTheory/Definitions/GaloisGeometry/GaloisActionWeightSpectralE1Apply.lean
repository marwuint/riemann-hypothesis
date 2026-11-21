import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PushWithIsTranspose
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castHQ_refl {E : Spc} {n i : ℤ} (x : HQ l E n i) : castHQ l (E := E) (rfl : n = n) (rfl : i = i) x = x := rfl

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

def castStr {t t' : ℕ} {n i n' i' : ℤ} (ht : t = t') (hn : n = n') (hi : i = i') :
    HQ l (sch.obj (Ystr J t)) n i ≃ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J t')) n' i' := by
  subst ht; subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castStr_refl {t : ℕ} {n i : ℤ} (x : HQ l (sch.obj (Ystr J t)) n i) :
    castStr l J (rfl : t = t) (rfl : n = n) (rfl : i = i) x = x := rfl

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

abbrev geomπ : GlobalTheory.Et.geom Ω p ⟶ V := pullback.fst _ _

abbrev geomFam : ι → (GlobalTheory.Et.geom Ω p).IdealSheafData := GlobalTheory.Strata.pull I (geomπ Ω p)

def galS (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) : GlobalTheory.Strata.Y (geomFam Ω p I) S ⟶ GlobalTheory.Strata.Y (geomFam Ω p I) S :=
  (pullIso I (geomπ Ω p) S).hom ≫
    pullback.map (geomπ Ω p) (Yι I S) (geomπ Ω p) (Yι I S) (GlobalTheory.Et.galMap Ω p σ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, GlobalTheory.Et.galMap_fst]) (by simp) ≫
    (pullIso I (geomπ Ω p) S).inv

@[reassoc (attr := simp)]
theorem galS_Yι (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) :
    galS Ω p I σ S ≫ Yι (geomFam Ω p I) S = Yι (geomFam Ω p I) S ≫ GlobalTheory.Et.galMap Ω p σ := by
  show _ ≫ Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S = Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S ≫ _
  rw [← pullIso_hom_fst I (geomπ Ω p) S]
  simp only [galS, Category.assoc, Iso.inv_hom_id_assoc, pullback.map, pullback.lift_fst]

def galStr (σ : Ω ≃ₐ[k] Ω) (t : ℕ) : Ystr (geomFam Ω p I) t ⟶ Ystr (geomFam Ω p I) t :=
  Sigma.desc fun S : Idx ι t => galS Ω p I σ S.1 ≫ inj _ S

@[reassoc (attr := simp)]
theorem inj_galStr (σ : Ω ≃ₐ[k] Ω) {t : ℕ} (S : Idx ι t) :
    inj _ S ≫ galStr Ω p I σ t = galS Ω p I σ S.1 ≫ inj _ S := Sigma.ι_desc _ _

variable (a b w : ℤ)

end Galois

end GlobalTheory.EtC.WSS

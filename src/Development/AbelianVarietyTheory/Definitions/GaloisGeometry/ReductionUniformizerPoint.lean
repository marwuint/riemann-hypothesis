import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

def ideal (S : Finset ι) : X.IdealSheafData := ⨆ i ∈ S, I i

theorem le_ideal {S : Finset ι} {i : ι} (h : i ∈ S) : I i ≤ ideal I S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => I i) i h

theorem ideal_mono {S S' : Finset ι} (h : S ⊆ S') : ideal I S ≤ ideal I S' :=
  iSup₂_le fun _ hi => le_ideal I (h hi)

@[simp] theorem ideal_empty : ideal I ∅ = ⊥ := by simp [ideal]

@[simp] theorem ideal_singleton (i : ι) : ideal I {i} = I i := by simp [ideal]

def Y (S : Finset ι) : Scheme.{0} := (ideal I S).subscheme

def Yι (S : Finset ι) : Y I S ⟶ X := (ideal I S).subschemeι

instance (S : Finset ι) : IsClosedImmersion (Yι I S) :=
  inferInstanceAs (IsClosedImmersion (ideal I S).subschemeι)

@[simp] theorem ker_Yι (S : Finset ι) : (Yι I S).ker = ideal I S := Scheme.IdealSheafData.ker_subschemeι _

def incl {S S' : Finset ι} (h : S ⊆ S') : Y I S' ⟶ Y I S :=
  Scheme.IdealSheafData.inclusion (ideal_mono I h)

@[reassoc (attr := simp)]
theorem incl_Yι {S S' : Finset ι} (h : S ⊆ S') : incl I h ≫ Yι I S = Yι I S' :=
  Scheme.IdealSheafData.inclusion_subschemeι _

@[simp]
theorem incl_refl (S : Finset ι) : incl I (subset_refl S) = 𝟙 (Y I S) :=
  Scheme.IdealSheafData.inclusion_id _

@[reassoc (attr := simp)]
theorem incl_comp {S S' S'' : Finset ι} (h : S ⊆ S') (h' : S' ⊆ S'') :
    incl I h' ≫ incl I h = incl I (h.trans h') :=
  Scheme.IdealSheafData.inclusion_comp _ _

instance {S S' : Finset ι} (h : S ⊆ S') : IsClosedImmersion (incl I h) := by
  have : IsClosedImmersion (incl I h ≫ Yι I S) := by rw [incl_Yι]; infer_instance
  exact IsClosedImmersion.of_comp (incl I h) (Yι I S)

abbrev Idx (ι : Type) (s : ℕ) : Type := {S : Finset ι // S.card = s + 1}

def Ystr (s : ℕ) : Scheme.{0} := ∐ fun S : Idx ι s => Y I S.1

def inj {s : ℕ} (S : Idx ι s) : Y I S.1 ⟶ Ystr I s := Sigma.ι (fun S : Idx ι s => Y I S.1) S

def Ystrπ (s : ℕ) : Ystr I s ⟶ X := Sigma.desc fun S : Idx ι s => Yι I S.1

@[reassoc (attr := simp)]
theorem inj_Ystrπ {s : ℕ} (S : Idx ι s) : inj I S ≫ Ystrπ I s = Yι I S.1 := Sigma.ι_desc _ _

theorem Ystr_hom_ext {s : ℕ} {Z : Scheme.{0}} {f g : Ystr I s ⟶ Z} (h : ∀ S : Idx ι s, inj I S ≫ f = inj I S ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

section Face

variable [LinearOrder ι]

def face {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : Idx ι s :=
  ⟨S.1.erase (S.1.orderEmbOfFin S.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), S.2]; rfl⟩

theorem face_subset {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : (face S j).1 ⊆ S.1 :=
  Finset.erase_subset _ _

def δ (s : ℕ) (j : Fin (s + 2)) : Ystr I (s + 1) ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι (s + 1) => incl I (face_subset S j) ≫ inj I (face S j)

@[reassoc (attr := simp)]
theorem inj_δ {s : ℕ} (j : Fin (s + 2)) (S : Idx ι (s + 1)) :
    inj I S ≫ δ I s j = incl I (face_subset S j) ≫ inj I (face S j) :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem δ_Ystrπ (s : ℕ) (j : Fin (s + 2)) : δ I s j ≫ Ystrπ I s = Ystrπ I (s + 1) :=
  Ystr_hom_ext I fun S => by simp

end Face

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section Fibre

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

def resMap : Spec (CommRingCat.of (O ⧸ Ideal.span {ϖ})) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ})))

instance : IsClosedImmersion (resMap ϖ) := by
  unfold resMap; exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of O) _

abbrev fibre : Scheme.{0} := pullback p (resMap ϖ)

def fibreIdeal : X.IdealSheafData := (pullback.fst p (resMap ϖ)).ker

def toFibre (S : Finset ι) (h : fibreIdeal p ϖ ≤ ideal I S) : Y I S ⟶ fibre p ϖ :=
  IsClosedImmersion.lift (pullback.fst p (resMap ϖ)) (Yι I S) (by rw [ker_Yι]; exact h)

@[reassoc (attr := simp)]
theorem toFibre_fst (S : Finset ι) (h : fibreIdeal p ϖ ≤ ideal I S) :
    toFibre I p ϖ S h ≫ pullback.fst p (resMap ϖ) = Yι I S :=
  IsClosedImmersion.lift_fac _ _ _

theorem fibreIdeal_le_ideal {S : Finset ι} (hS : S.Nonempty) (h : ∀ i, fibreIdeal p ϖ ≤ I i) :
    fibreIdeal p ϖ ≤ ideal I S := by
  obtain ⟨i, hi⟩ := hS
  exact (h i).trans (le_ideal I hi)

@[reassoc (attr := simp)]
theorem incl_toFibre {S S' : Finset ι} (hSS : S ⊆ S') (h : fibreIdeal p ϖ ≤ ideal I S) :
    incl I hSS ≫ toFibre I p ϖ S h = toFibre I p ϖ S' (h.trans (ideal_mono I hSS)) :=
  (cancel_mono (pullback.fst p (resMap ϖ))).1 (by simp)

end Fibre

section BaseChange

variable {X' : Scheme.{0}} (f : X' ⟶ X)

def pull : ι → X'.IdealSheafData := fun i => (I i).comap f

theorem ideal_pull (S : Finset ι) : ideal (pull I f) S = (ideal I S).comap f := by
  unfold ideal pull
  exact ((Scheme.IdealSheafData.map_gc f).l_iSup₂).symm

def isoOfEq {J J' : X.IdealSheafData} (e : J = J') : J.subscheme ≅ J'.subscheme where
  hom := Scheme.IdealSheafData.inclusion e.ge
  inv := Scheme.IdealSheafData.inclusion e.le
  hom_inv_id := by simp
  inv_hom_id := by simp

def pullIso (S : Finset ι) : Y (pull I f) S ≅ pullback f (Yι I S) :=
  isoOfEq (ideal_pull I f S) ≪≫ Scheme.IdealSheafData.comapIso (ideal I S) f

@[reassoc (attr := simp)]
theorem pullIso_hom_fst (S : Finset ι) : (pullIso I f S).hom ≫ pullback.fst _ _ = Yι (pull I f) S := by
  change (isoOfEq (ideal_pull I f S)).hom ≫ (Scheme.IdealSheafData.comapIso (ideal I S) f).hom ≫ pullback.fst _ _ = _
  rw [Scheme.IdealSheafData.comapIso_hom_fst]
  exact Scheme.IdealSheafData.inclusion_subschemeι _

def pullMap (S : Finset ι) : Y (pull I f) S ⟶ Y I S := (pullIso I f S).hom ≫ pullback.snd _ _

@[reassoc (attr := simp)]
theorem pullMap_Yι (S : Finset ι) : pullMap I f S ≫ Yι I S = Yι (pull I f) S ≫ f := by
  simp [pullMap, ← pullback.condition]

end BaseChange

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section FibreStr

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

def YstrToFibre (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) : Ystr I s ⟶ fibre p ϖ :=
  Sigma.desc fun S : Idx ι s =>
    toFibre I p ϖ S.1 (fibreIdeal_le_ideal I p ϖ (Finset.card_pos.1 (by rw [S.2]; omega)) h)

@[reassoc (attr := simp)]
theorem inj_YstrToFibre (h : ∀ i, fibreIdeal p ϖ ≤ I i) {s : ℕ} (S : Idx ι s) :
    inj I S ≫ YstrToFibre I p ϖ h s =
      toFibre I p ϖ S.1 (fibreIdeal_le_ideal I p ϖ (Finset.card_pos.1 (by rw [S.2]; omega)) h) :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem YstrToFibre_fst (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) :
    YstrToFibre I p ϖ h s ≫ pullback.fst p (resMap ϖ) = Ystrπ I s :=
  Ystr_hom_ext I fun S => by simp

@[reassoc (attr := simp)]
theorem δ_YstrToFibre [LinearOrder ι] (h : ∀ i, fibreIdeal p ϖ ≤ I i) (s : ℕ) (j : Fin (s + 2)) :
    δ I s j ≫ YstrToFibre I p ϖ h s = YstrToFibre I p ϖ h (s + 1) :=
  (cancel_mono (pullback.fst p (resMap ϖ))).1 (by simp)

end FibreStr

section BaseChangeStr

variable {X' : Scheme.{0}} (f : X' ⟶ X)

@[reassoc (attr := simp)]
theorem incl_pullMap {S S' : Finset ι} (h : S ⊆ S') :
    incl (pull I f) h ≫ pullMap I f S = pullMap I f S' ≫ incl I h :=
  (cancel_mono (Yι I S)).1 (by simp)

def pullStr (s : ℕ) : Ystr (pull I f) s ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι s => pullMap I f S.1 ≫ inj I S

@[reassoc (attr := simp)]
theorem inj_pullStr {s : ℕ} (S : Idx ι s) : inj (pull I f) S ≫ pullStr I f s = pullMap I f S.1 ≫ inj I S :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
theorem pullStr_Ystrπ (s : ℕ) : pullStr I f s ≫ Ystrπ I s = Ystrπ (pull I f) s ≫ f :=
  Ystr_hom_ext _ fun S => by simp

end BaseChangeStr

end GlobalTheory.Strata

namespace GlobalTheory.Strata.Example

end GlobalTheory.Strata.Example

namespace GlobalTheory.Strata

end GlobalTheory.Strata

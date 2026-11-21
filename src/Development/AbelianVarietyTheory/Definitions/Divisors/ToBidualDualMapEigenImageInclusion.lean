import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.VB

namespace GlobalTheory.LieVB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {O : Type} [CommRing O]

variable (F) in

@[reassoc (attr := simp)] theorem toBidual_dual_comp_dualMap :
    cartierDualToBidual (dual F) ≫ dualMap (cartierDualToBidual F) = 𝟙 _ := by
  ext V l : 3
  exact dual_ext fun W h s => congrArg (dualApp l h) (resM_self _ s)

instance mono_toBidual_dual : Mono (cartierDualToBidual (dual F)) :=
  mono_of_mono_fac (toBidual_dual_comp_dualMap F)

theorem mono_toBidual_of_mono (i : G ⟶ F) [Mono i] [Mono (cartierDualToBidual F)] : Mono (cartierDualToBidual G) :=
  mono_of_mono_fac (toBidual_naturality_dualSheafTranspose i).symm

theorem mono_toBidual_of_isVectorBundle {r : ℕ} (h : IsVB F r) : Mono (cartierDualToBidual F) :=
  have := h.isIso_toBidual_of_local_frames
  inferInstance

def IsRegularFn (D : Γ(X, ⊤)) : Prop :=
  ∀ (V : X.Opens) (a : Γ(X, V)), resG X (le_top : V ≤ ⊤) D * a = 0 → a = 0

theorem IsRegularFn.eq_zero_of_smul {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {V : X.Opens} {s : Γ(F, V)} (e : resG X (le_top : V ≤ ⊤) D • s = 0) : s = 0 := by
  refine QCoh.injective_app_of_mono (cartierDualToBidual F) V (Eq.trans ?_ (map_zero _).symm)
  refine dual_ext fun W hW l => h W _ ?_
  have := congrArg (fun t => dualApp l le_rfl (resM F hW t)) e
  simp only [resM_smul, map_smul, resG_resG, map_zero] at this
  exact this

theorem IsRegularFn.hom_eq_zero {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {φ : G ⟶ F} (e : D • φ = 0) : φ = 0 := by
  ext V s : 3
  exact h.eq_zero_of_smul congr(($e).app V s)

section Im

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

def eigenEval : F ⟶ dual (eigen (dualAct ρ) σ) := cartierDualToBidual F ≫ dualMap (eigenι (dualAct ρ) σ)

theorem dualApp_eigenEval {V W : X.Opens} (s : Γ(F, V)) (h : W ≤ V)
    (l : Γ(eigen (dualAct ρ) σ, W)) : dualApp ((eigenEval ρ σ).app V s) h l =
      dualApp ((eigenι (dualAct ρ) σ).app W l) le_rfl (resM F h s) := rfl

theorem eigenEval_eq : eigenEval ρ σ =
    eigenπ ρ σ ≫ cartierDualToBidual _ ≫ dualMap (dualQuotIso ρ σ).inv := by
  rw [toBidual_naturality_dualSheafTranspose_assoc, ← dualMap_comp, ← dualQuotIso_hom_ι, Iso.inv_hom_id_assoc,
    eigenEval]

def eigenIm : X.Modules := image (eigenEval ρ σ)

def eigenImπ : F ⟶ eigenIm ρ σ := factorThruImage _

def eigenImι : eigenIm ρ σ ⟶ dual (eigen (dualAct ρ) σ) := image.ι _

instance epi_eigenImπ : Epi (eigenImπ ρ σ) := inferInstanceAs (Epi (factorThruImage _))

instance mono_eigenImι : Mono (eigenImι ρ σ) := inferInstanceAs (Mono (image.ι _))

@[reassoc (attr := simp)] theorem eigenImπ_ι : eigenImπ ρ σ ≫ eigenImι ρ σ = eigenEval ρ σ :=
  image.fac _

instance mono_toBidual_eigenImage : Mono (cartierDualToBidual (eigenIm ρ σ)) :=
  mono_toBidual_of_mono (eigenImι ρ σ)

theorem act_eigenImπ (a : O) : act ρ a ≫ eigenImπ ρ σ = σ a • eigenImπ ρ σ := by
  rw [← cancel_mono (eigenImι ρ σ), Category.assoc, Linear.smul_comp, eigenImπ_ι, eigenEval_eq,
    ← Category.assoc, act_eigenπ, Linear.smul_comp]

def quotToIm : eigenQuot ρ σ ⟶ eigenIm ρ σ := eigenDesc (eigenImπ ρ σ) (act_eigenImπ ρ σ)

@[reassoc (attr := simp)] theorem eigenπ_quotToIm : eigenπ ρ σ ≫ quotToIm ρ σ = eigenImπ ρ σ :=
  eigenπ_desc _ _ _ _

instance epi_quotToIm : Epi (quotToIm ρ σ) := epi_of_epi_fac (eigenπ_quotToIm ρ σ)

variable {ρ σ}

theorem comp_eq_zero_of_comp_eigenImπ [Mono (cartierDualToBidual G)] {φ : F ⟶ G}
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) {k : H ⟶ F} (hk : k ≫ eigenImπ ρ σ = 0) : k ≫ φ = 0 := by
  have h' (a : O) : dualMap φ ≫ act (dualAct ρ) a = σ a • dualMap φ := by
    rw [act_dualAct, ← dualMap_comp, h, dualMap_smul]
  rw [← cancel_mono (cartierDualToBidual G), Category.assoc, toBidual_naturality_dualSheafTranspose, ← eigenLift_ι _ _ _ h',
    dualMap_comp, zero_comp, ← Category.assoc (cartierDualToBidual F), ← eigenEval, ← eigenImπ_ι,
    Category.assoc, reassoc_of% hk, zero_comp]

def eigenImDesc [Mono (cartierDualToBidual G)] (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenIm ρ σ ⟶ G :=
  Abelian.epiDesc (eigenImπ ρ σ) φ (comp_eq_zero_of_comp_eigenImπ h (kernel.condition _))

@[reassoc (attr := simp)] theorem eigenImπ_desc [Mono (cartierDualToBidual G)] (φ : F ⟶ G)
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) : eigenImπ ρ σ ≫ eigenImDesc φ h = φ :=
  Abelian.comp_epiDesc _ _ _

variable {ρ' : O →+* End G} (σ)

def eigenImMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) : eigenIm ρ σ ⟶ eigenIm ρ' σ :=
  eigenImDesc (φ ≫ eigenImπ ρ' σ) fun a => by
    rw [← Category.assoc, h a, Category.assoc, act_eigenImπ, Linear.comp_smul]

@[reassoc (attr := simp)] theorem eigenImπ_eigenImMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    eigenImπ ρ σ ≫ eigenImMap σ h = φ ≫ eigenImπ ρ' σ := eigenImπ_desc _ _

instance epi_eigenImMap {φ : F ⟶ G} [Epi φ] (h : IsEquivariant ρ ρ' φ) : Epi (eigenImMap σ h) :=
  epi_of_epi_fac (eigenImπ_eigenImMap σ h)

@[simps] def eigenImIso {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    eigenIm ρ σ ≅ eigenIm ρ' σ where
  hom := eigenImMap σ h
  inv := eigenImMap σ (isEquivariant_inv h)
  hom_inv_id := by rw [← cancel_epi (eigenImπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenImπ _ _)]; simp

variable (ρ)

def eigenImConjIso {c : O →+* O} (hc : Function.Involutive c) :
    eigenIm (ρ.comp c) σ ≅ eigenIm ρ (σ.comp c) where
  hom := eigenImDesc (eigenImπ _ _) fun a => by
    have := act_eigenImπ ρ (σ.comp c) (c a)
    rwa [RingHom.comp_apply, hc] at this
  inv := eigenImDesc (eigenImπ _ _) fun a => by
    have := act_eigenImπ (ρ.comp c) σ (c a)
    rwa [act, RingHom.comp_apply, hc] at this
  hom_inv_id := by rw [← cancel_epi (eigenImπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenImπ _ _)]; simp

@[reassoc (attr := simp)] theorem eigenImπ_eigenImConjIso_hom {c : O →+* O}
    (hc : Function.Involutive c) : eigenImπ _ _ ≫ (eigenImConjIso ρ σ hc).hom = eigenImπ _ _ := by
  simp only [eigenImConjIso, eigenImπ_desc]

theorem toBidual_dualMap_eigenImage_inclusion : (cartierDualToBidual _ ≫ dualMap (eigenImι ρ σ)) ≫
    dualMap (eigenImπ ρ σ) = eigenι (dualAct ρ) σ := by
  rw [Category.assoc, ← dualMap_comp, eigenImπ_ι, eigenEval, dualMap_comp,
    ← toBidual_naturality_dualSheafTranspose_assoc, toBidual_dual_comp_dualMap, Category.comp_id]

def dualImIso : dual (eigenIm ρ σ) ≅ eigen (dualAct ρ) σ where
  hom := eigenLift (dualMap (eigenImπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenImπ, dualMap_smul]
  inv := cartierDualToBidual _ ≫ dualMap (eigenImι ρ σ)
  hom_inv_id := by
    rw [← cancel_mono (dualMap (eigenImπ ρ σ)), Category.assoc, toBidual_dualMap_eigenImage_inclusion,
      eigenLift_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (eigenι _ _), Category.assoc, eigenLift_ι, toBidual_dualMap_eigenImage_inclusion,
      Category.id_comp]

@[reassoc (attr := simp)] theorem dualImIso_hom_ι :
    (dualImIso ρ σ).hom ≫ eigenι _ _ = dualMap (eigenImπ ρ σ) := rfl

variable {ρ σ}

end Im

section Proj

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

structure IsEigenProj (ε : F ⟶ F) (D : Γ(X, ⊤)) : Prop where

  act_comp : ∀ a, act ρ a ≫ ε = σ a • ε

  exists_sum : ∃ (n : ℕ) (c : Fin n → Γ(X, ⊤)) (b : Fin n → O),
    ε = ∑ i, c i • act ρ (b i) ∧ D = ∑ i, c i * σ (b i)

variable {ρ σ}

namespace IsEigenProj

variable {ε : F ⟶ F} {D : Γ(X, ⊤)} (h : IsEigenProj ρ σ ε D)
include h

theorem comp_eq_smul {φ : F ⟶ G} (hφ : ∀ a, act ρ a ≫ φ = σ a • φ) : ε ≫ φ = D • φ := by
  obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
  simp only [Preadditive.sum_comp, Linear.smul_comp, hφ, Finset.sum_smul, mul_smul]

theorem isEquivariant : IsEquivariant ρ ρ ε := fun a => by
  obtain ⟨n, c, b, rfl, -⟩ := h.exists_sum
  have e (x : O) : act ρ a ≫ act ρ x = act ρ x ≫ act ρ a :=
    (map_mul ρ x a).symm.trans ((congrArg ρ (mul_comm x a)).trans (map_mul ρ a x))
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp, e]

theorem comp_act (a : O) : ε ≫ act ρ a = σ a • ε := (h.isEquivariant a).symm.trans (h.act_comp a)

theorem pullback (f : Y ⟶ X) : IsEigenProj (pullAct ρ f) (f.appTop.hom.comp σ)
    ((Scheme.Modules.pullback f).map ε) (f.appTop D) where
  act_comp a := by rw [act_pullAct, ← Functor.map_comp, h.act_comp, pullback_map_smul]; rfl
  exists_sum := by
    obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
    refine ⟨n, fun i => f.appTop (c i), b, ?_, by simp⟩
    rw [Functor.map_sum]
    exact Finset.sum_congr rfl fun i _ => pullback_map_smul _ _ _

theorem comp_eigenImπ_eq_zero (hD : IsRegularFn D) {k : G ⟶ F} (hk : k ≫ ε = 0) :
    k ≫ eigenImπ ρ σ = 0 :=
  hD.hom_eq_zero (by
    rw [← Linear.comp_smul, ← h.comp_eq_smul (act_eigenImπ ρ σ), reassoc_of% hk, zero_comp])

variable [Mono (cartierDualToBidual F)]

def imToSub : eigenIm ρ σ ⟶ eigen ρ σ :=
  eigenLift (eigenImDesc ε h.act_comp) fun a => by
    rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_desc_assoc, Linear.comp_smul, eigenImπ_desc,
      h.comp_act]

@[reassoc (attr := simp)] theorem eigenImπ_imToSub_ι :
    eigenImπ ρ σ ≫ h.imToSub ≫ eigenι ρ σ = ε := eigenImπ_desc _ h.act_comp

theorem imToSub_ι_eigenImπ : h.imToSub ≫ eigenι ρ σ ≫ eigenImπ ρ σ = D • 𝟙 _ := by
  rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_imToSub_ι_assoc, h.comp_eq_smul (act_eigenImπ ρ σ),
    Linear.comp_smul, Category.comp_id]

variable (hD : IsRegularFn D)
include hD

theorem mono_imToSub : Mono h.imToSub :=
  Preadditive.mono_of_cancel_zero _ fun g hg => hD.hom_eq_zero (by
    rw [← Category.comp_id g, ← Linear.comp_smul, ← h.imToSub_ι_eigenImπ, reassoc_of% hg, zero_comp])

def imIsoImage : eigenIm ρ σ ≅ image ε :=
  have := h.mono_imToSub hD
  have := strongEpi_of_epi (eigenImπ ρ σ)
  image.isoStrongEpiMono (eigenImπ ρ σ) (h.imToSub ≫ eigenι ρ σ) h.eigenImπ_imToSub_ι

@[reassoc (attr := simp)] theorem imIsoImage_hom_ι :
    (h.imIsoImage hD).hom ≫ image.ι ε = h.imToSub ≫ eigenι ρ σ :=
  have := h.mono_imToSub hD
  have := strongEpi_of_epi (eigenImπ ρ σ)
  image.isoStrongEpiMono_hom_comp_ι _ _ h.eigenImπ_imToSub_ι

omit hD

variable (f : Y ⟶ X) (hf : IsRegularFn (f.appTop D))

def pullbackImHom : (Scheme.Modules.pullback f).obj (eigenIm ρ σ) ⟶
    eigenIm (pullAct ρ f) (f.appTop.hom.comp σ) :=
  Abelian.epiDesc ((Scheme.Modules.pullback f).map (eigenImπ ρ σ)) (eigenImπ _ _)
    ((h.pullback f).comp_eigenImπ_eq_zero hf (by
      rw [← h.eigenImπ_imToSub_ι, Functor.map_comp, kernel.condition_assoc, zero_comp]))

@[reassoc (attr := simp)] theorem map_eigenImπ_pullbackImHom :
    (Scheme.Modules.pullback f).map (eigenImπ ρ σ) ≫ h.pullbackImHom f hf = eigenImπ _ _ :=
  Abelian.comp_epiDesc _ _ _

instance epi_pullbackImHom : Epi (h.pullbackImHom f hf) :=
  epi_of_epi_fac (h.map_eigenImπ_pullbackImHom f hf)

variable [Mono (cartierDualToBidual ((Scheme.Modules.pullback f).obj F))]

end IsEigenProj

end Proj

end GlobalTheory.LieVB

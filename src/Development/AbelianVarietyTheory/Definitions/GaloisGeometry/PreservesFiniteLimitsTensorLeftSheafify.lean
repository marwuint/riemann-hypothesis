import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsGrothendieckAbelianPresheaf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory Enriched.FunctorCategory
open scoped MonoidalClosed

namespace GlobalTheory.Et

section Site

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasFunctorEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance (F G : Cᵒᵖ ⥤ ModuleCat.{1} S) : HasEnrichedHom (ModuleCat.{1} S) F G := inferInstance

instance : (J.W (A := ModuleCat.{1} S)).IsMonoidal := GrothendieckTopology.W.monoidal

instance : MonoidalClosed (Cᵒᵖ ⥤ ModuleCat.{1} S) := MonoidalClosed.FunctorCategory.monoidalClosed

theorem preservesFiniteLimits_tensorLeft_presheaf (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft P) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
  intro U
  have : Module.Flat S (P.obj U) := hP U
  have e : (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U ⋙ tensorLeft (P.obj U) ≅
      tensorLeft P ⋙ (evaluation Cᵒᵖ (ModuleCat.{1} S)).obj U := NatIso.ofComponents (fun F => Iso.refl _) (by
        intro F G g
        simp)
  exact preservesLimitsOfShape_of_natIso e

variable [HasSheafify J (ModuleCat.{1} S)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

def tensorLeftSheafifyIso (P : Cᵒᵖ ⥤ ModuleCat.{1} S) :
    tensorLeft ((presheafToSheaf J _).obj P) ≅ sheafToPresheaf J _ ⋙ tensorLeft P ⋙ presheafToSheaf J _ :=
  NatIso.ofComponents (fun F => whiskerLeftIso _ (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J _) P F.obj) (by
    intro F G g
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, asIso_inv, Functor.Monoidal.μIso_hom]
    have h : g ≫ inv ((sheafificationAdjunction J _).counit.app G) =
        inv ((sheafificationAdjunction J _).counit.app F) ≫ (presheafToSheaf J _).map ((sheafToPresheaf J _).map g) := by
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact ((sheafificationAdjunction J _).counit.naturality g).symm
    change _ ◁ g ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ (sheafToPresheaf J _).map g)
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h, MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (Functor.LaxMonoidal.μ_natural_right (presheafToSheaf J (ModuleCat.{1} S)) P
      ((sheafToPresheaf J _).map g)))

theorem preservesFiniteLimits_tensorLeft_sheafify (P : Cᵒᵖ ⥤ ModuleCat.{1} S) (hP : ∀ U, Module.Flat S (P.obj U)) :
    PreservesFiniteLimits (tensorLeft ((presheafToSheaf J _).obj P)) := by
  have := preservesFiniteLimits_tensorLeft_presheaf S P hP
  exact preservesFiniteLimits_of_natIso (tensorLeftSheafifyIso J S P).symm

end Site

section Lin

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

instance tensorLeft_presheaf_additive (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Additive where
  map_add {F G} f g := by
    ext U : 2
    exact MonoidalPreadditive.whiskerLeft_add ..

instance tensorLeft_presheaf_linear (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : (tensorLeft P).Linear S where
  map_smul {F G} f r := by
    ext U : 2
    exact MonoidalLinear.whiskerLeft_smul ..

variable [HasSheafify J (ModuleCat.{1} S)]

instance presheafToSheaf_linear : (presheafToSheaf J (ModuleCat.{1} S)).Linear S where
  map_smul {P Q} f r := by
    let adj := sheafificationAdjunction J (ModuleCat.{1} S)
    apply (adj.homEquiv P ((presheafToSheaf J _).obj Q)).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit]
    have h1 := adj.unit.naturality (r • f)
    have h2 := adj.unit.naturality f
    dsimp at h1 h2
    change adj.unit.app P ≫ ((presheafToSheaf J (ModuleCat.{1} S)).map (r • f)).hom =
      adj.unit.app P ≫ (r • ((presheafToSheaf J (ModuleCat.{1} S)).map f).hom)
    rw [Linear.comp_smul, ← h2, ← h1, Linear.smul_comp]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

theorem tensorLeft_sheaf_additive (F : Sheaf J (ModuleCat.{1} S)) : (tensorLeft F).Additive := by
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.additive_of_iso e.symm

theorem tensorLeft_sheaf_linear (F : Sheaf J (ModuleCat.{1} S)) :
    letI := tensorLeft_sheaf_additive J S F
    (tensorLeft F).Linear S := by
  letI := tensorLeft_sheaf_additive J S F
  have e : tensorLeft F ≅ sheafToPresheaf J _ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _ :=
    (tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app F)).symm ≪≫
      tensorLeftSheafifyIso J S F.obj
  exact Functor.linear_of_iso S e.symm

end Lin

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

instance : MonoidalCategory (Shv R) := Sheaf.monoidalCategory _ _

instance : SymmetricCategory (Shv R) := Sheaf.symmetricCategory _ _

instance : MonoidalClosed (Shv R) := Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance (F : Shv R) : (tensorLeft F).Additive := tensorLeft_sheaf_additive _ _ F

instance (F : Shv R) : (tensorLeft F).Linear (ULift.{1} R) := tensorLeft_sheaf_linear _ _ F

instance (F : Shv R) : (tensorRight F).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : (tensorRight F).Linear (ULift.{1} R) :=
  Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight F)

instance (F : Shv R) : PreservesFiniteColimits (tensorRight F) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

abbrev freePre (X : Scheme.{0}) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) :=
  uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)

instance (X : Scheme.{0}) : PreservesFiniteLimits (tensorLeft ((freeOn R).obj X)) :=
  preservesFiniteLimits_tensorLeft_sheafify _ _ (freePre R X) (fun U =>
    inferInstanceAs (Module.Flat (ULift.{1} R) (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R)))

class FlatCoef : Prop where
  preservesFiniteLimits_tensorRight : PreservesFiniteLimits (tensorRight (coef R))

attribute [instance] FlatCoef.preservesFiniteLimits_tensorRight

theorem FlatCoef.of_flat (h : ∀ U : Scheme.{0}, Module.Flat R C(U, R)) : FlatCoef R := by
  have : PreservesFiniteLimits (tensorLeft (coef R)) :=
    preservesFiniteLimits_tensorLeft_sheafify _ _ (coefPre R) (fun U => by
      have := h U.unop
      change Module.Flat (ULift.{1} R) (ULift.{1} C(U.unop, R))
      rw [Module.Flat.ulift_left_iff]
      infer_instance)
  exact ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (coef R))⟩

instance [IsDomain R] [IsBezout R] : FlatCoef R := by
  refine FlatCoef.of_flat R fun U => ?_
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro f hf
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff f).1 hf
  ext u
  have hu := congrArg (fun g : C(U, R) => g u) ha
  simp only [Submonoid.smul_def, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.zero_apply] at hu
  exact (mul_eq_zero.1 hu).resolve_left (nonZeroDivisors.ne_zero a.2)

def coefMulPre : coefPre R ⊗ coefPre R ⟶ coefPre R where
  app U := ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ (ULift.{1} R)
    (fun f g : ULift.{1} C(U.unop, R) => (⟨f.down * g.down⟩ : ULift.{1} C(U.unop, R)))
    (fun _ _ _ => ULift.ext _ _ (add_mul _ _ _))
    (fun c _ _ => ULift.ext _ _ (smul_mul_assoc c.down _ _))
    (fun _ _ _ => ULift.ext _ _ (mul_add _ _ _))
    (fun c _ _ => ULift.ext _ _ (mul_smul_comm c.down _ _))))
  naturality U V f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl

def freeDiagPre (X : Scheme.{0}) : freePre R X ⟶ freePre R X ⊗ freePre R X where
  app U := ModuleCat.ofHom (Finsupp.linearCombination (ULift.{1} R)
    (fun f => ((Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U) ⊗ₜ[ULift.{1} R]
      (Finsupp.single f (1 : ULift.{1} R) : (freePre R X).obj U))))
  naturality U V g := by
    apply ModuleCat.hom_ext
    refine Finsupp.lhom_ext (fun f c => ?_)
    change Finsupp.linearCombination _ _ (Finsupp.mapDomain _ (Finsupp.single f c)) =
      ((freePre R X ⊗ freePre R X).map g).hom (Finsupp.linearCombination _ _ (Finsupp.single f c))
    rw [Finsupp.mapDomain_single]
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
    congr 1
    exact (congrArg₂ (fun (a b : (freePre R X).obj V) => a ⊗ₜ[ULift.{1} R] b) Finsupp.mapDomain_single Finsupp.mapDomain_single).symm

def coefMul : coef R ⊗ coef R ⟶ coef R :=
  Functor.LaxMonoidal.μ (presheafToSheaf _ _) (coefPre R) (coefPre R) ≫ (presheafToSheaf _ _).map (coefMulPre R)

def freeDiag (X : Scheme.{0}) : (freeOn R).obj X ⟶ (freeOn R).obj X ⊗ (freeOn R).obj X :=
  (presheafToSheaf _ _).map (freeDiagPre R X) ≫ Functor.OplaxMonoidal.δ (presheafToSheaf _ _) _ _

section Cup

variable [FlatCoef R]

def cupExt (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X) (b : HS R (coef R) j X) :
    HS R (coef R) n X :=
  (Abelian.Ext.mk₀ (freeDiag R X)).comp ((b.mapExactFunctor (tensorLeft ((freeOn R).obj X))).comp
    ((a.mapExactFunctor (tensorRight (coef R))).comp (Abelian.Ext.mk₀ (coefMul R)) (add_zero i))
    (show j + i = n by omega)) (zero_add n)

theorem cupExt_add_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a a' : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (a + a') b = cupExt R X h a b + cupExt R X h a' b := by
  simp only [cupExt, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

theorem cupExt_add_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (a : HS R (coef R) i X)
    (b b' : HS R (coef R) j X) : cupExt R X h a (b + b') = cupExt R X h a b + cupExt R X h a b' := by
  simp only [cupExt, Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

theorem cupExt_smul_left (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h (r • a) b = r • cupExt R X h a b := by
  simp only [cupExt, Functor.mapExactFunctor_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul]

theorem cupExt_smul_right (X : Scheme.{0}) {i j n : ℕ} (h : i + j = n) (r : ULift.{1} R) (a : HS R (coef R) i X)
    (b : HS R (coef R) j X) : cupExt R X h a (r • b) = r • cupExt R X h a b := by
  simp only [cupExt, Functor.mapExactFunctor_smul, Abelian.Ext.smul_comp, Abelian.Ext.comp_smul]

def cupN (X : Scheme.{0}) (i j n : ℕ) (h : i + j = n) : H R i X →ₗ[R] H R j X →ₗ[R] H R n X :=
  LinearMap.mk₂ R (fun a b => cupExt R X h a b)
    (fun a a' b => cupExt_add_left R X h a a' b)
    (fun r a b => cupExt_smul_left R X h (ULift.up r) a b)
    (fun a b b' => cupExt_add_right R X h a b b')
    (fun r a b => cupExt_smul_right R X h (ULift.up r) a b)

def cup (X : Scheme.{0}) (i j : ℕ) : H R i X →ₗ[R] H R j X →ₗ[R] H R (i + j) X := cupN R X i j (i + j) rfl

theorem cupN_apply (X : Scheme.{0}) (i j n : ℕ) (h : i + j = n) (a : H R i X) (b : H R j X) :
    cupN R X i j n h a b = cupExt R X h a b := rfl

theorem cup_eq_cupN (X : Scheme.{0}) (i j : ℕ) : cup R X i j = cupN R X i j (i + j) rfl := rfl

end Cup

end GlobalTheory.Et

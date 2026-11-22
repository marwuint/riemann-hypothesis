import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoCechComplexMapPresheafCubeRes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfIsLocalizedModuleRes

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe t v u

noncomputable section

namespace GlobalTheory

variable {X Y : Scheme.{u}} {ι : Type}

section Basic

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps]
def sectionsPresheafMap {F G : X.Modules} (φ : F ⟶ G) :
    sectionsPresheaf R F ⟶ sectionsPresheaf R G where
  app W := ModuleCat.ofHom (sectionsOn.map R φ W.unop)
  naturality _ _ i := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (sectionsOn.res_map R φ i.unop.le x).symm)

theorem isSheaf_sectionsPresheaf (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (sectionsPresheaf R F) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{u} R)
    (X := X.toPresheafedSpace.carrier) (sectionsPresheaf R F)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{u}) F.presheaf).1
      F.isSheaf)

@[simp]
theorem sectionsOn.res_res (F : X.Modules) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : sectionsOn F W) :
    sectionsOn.res R F h' (sectionsOn.res R F h x) = sectionsOn.res R F (h'.trans h) x :=
  LinearMap.congr_fun (sectionsOn.res_comp_res R F h h') x

def sectionsOn.congrOpens (F : X.Modules) {W W' : X.Opens} (h : W = W') :
    sectionsOn F W ≃ₗ[R] sectionsOn F W' :=
  presheafCongr (sectionsPresheaf R F) h

@[simp]
theorem sectionsOn.congrOpens_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W) : sectionsOn.congrOpens R F h x = sectionsOn.res R F h.ge x := rfl

@[simp]
theorem sectionsOn.congrOpens_symm_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W') :
    (sectionsOn.congrOpens R F h).symm x = sectionsOn.res R F h.le x := rfl

variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechCube : Cube.{u} ι R := presheafCube (sectionsPresheaf R F) V U

variable {F} in

def cechCubeMap (φ : F ⟶ G) : cechCube R F V U ⟶ cechCube R G V U :=
  presheafCubeMap V U (sectionsPresheafMap R φ)

variable {F} in

@[simp]
theorem cechCubeMap_app (φ : F ⟶ G) (s : Finset ι) :
    ((cechCubeMap R V U φ).app s).hom = sectionsOn.map R φ (cechOpen V U s) := rfl

@[simps]
def cechCubeFunctor : X.Modules ⥤ Cube.{u} ι R where
  obj F := cechCube R F V U
  map := cechCubeMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechCubeFunctor_additive : (cechCubeFunctor R V U).Additive where
  map_add := rfl

variable {V U} in

def cechCubeRes {V' : X.Opens} {U' : ι → X.Opens} (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    cechCube R F V U ⟶ cechCube R F V' U' :=
  presheafCubeRes (sectionsPresheaf R F) h

variable {V U} in

@[simp]
theorem cechCubeRes_app {V' : X.Opens} {U' : ι → X.Opens}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((cechCubeRes R F h).app s).hom = sectionsOn.res R F (h s) := rfl

def cechRestrictions : sectionsOn F V →ₗ[R] Cube.Term (cechCube R F V U) 1 :=
  presheafCechAug (sectionsPresheaf R F) V U

@[simp]
theorem cechRestrictions_apply (x : sectionsOn F V) (s : {s : Finset ι // s.card = 1}) :
    cechRestrictions R F V U x s = sectionsOn.res R F (cechOpen_le V U s.1) x := rfl

variable [LinearOrder ι]

def cech : CochainComplex (ModuleCat.{u} R) ℕ := cechComplex (cechCube R F V U)

def cechH (n : ℕ) : ModuleCat.{u} R := (cech R F V U).homology n

theorem cech_def : cech R F V U = cechComplex (cechCube R F V U) := rfl

theorem cechH_def (n : ℕ) : cechH R F V U n = (cech R F V U).homology n := rfl

theorem cech_X (p : ℕ) : (cech R F V U).X p = ModuleCat.of R
    (∀ s : {s : Finset ι // s.card = p + 1}, sectionsOn F (V ⊓ ⨅ i ∈ s.1, U i)) := rfl

variable {F} in

def cechMap (φ : F ⟶ G) : cech R F V U ⟶ cech R G V U := cechComplexMap (cechCubeMap R V U φ)

variable {F} in

def cechHMap (φ : F ⟶ G) (n : ℕ) : cechH R F V U n ⟶ cechH R G V U n :=
  HomologicalComplex.homologyMap (cechMap R V U φ) n

@[simps]
def cechModulesFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj F := cech R F V U
  map := cechMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechModulesFunctor_additive : (cechModulesFunctor R V U).Additive where
  map_add := rfl

@[simps]
def cechHFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := cechH R F V U n
  map φ := cechHMap R V U φ n
  map_id F := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id F
  map_comp := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp

instance cechHFunctor_additive (n : ℕ) : (cechHFunctor R V U n).Additive where
  map_add := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add

@[simp]
theorem cechMap_id : cechMap R V U (𝟙 F) = 𝟙 _ := rfl

variable {F} in

@[reassoc]
theorem cechMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    cechMap R V U (φ ≫ ψ) = cechMap R V U φ ≫ cechMap R V U ψ := rfl

@[simp]
theorem cechHMap_id (n : ℕ) : cechHMap R V U (𝟙 F) n = 𝟙 _ := (cechHFunctor R V U n).map_id F

theorem cechHMap_smulHom_apply (r : R) (n : ℕ) (x : cechH R F V U n) :
    (cechHMap R V U (smulHom F (algebraMap R Γ(X, ⊤) r)) n).hom x = r • x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective (cechCube R F V U) n x
  exact (homologyMap_cechClass (cechCubeMap R V U _) n x (r • x) rfl).trans
    (map_smul (cechClass (cechCube R F V U) n) r x)

theorem cechModulesFunctor_shortExact (S : ShortComplex X.Modules)
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (cechOpen V U s)) ∧
      Function.Exact (S.f.app (cechOpen V U s)) (S.g.app (cechOpen V U s)) ∧
      Function.Surjective (S.g.app (cechOpen V U s))) :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechCubeFunctor R V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2

theorem isZero_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero (cechH R F V U n) := isZero_cechComplex_homology _ h

theorem subsingleton_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    Subsingleton (cechH R F V U n) := ModuleCat.isZero_iff_subsingleton.1 (isZero_cechH R F V U h)

variable {V U} in

def cechTopIso (h : ∀ i, U i ≤ V) : cech R F ⊤ U ≅ cech R F V U :=
  presheafCechTopIso (sectionsPresheaf R F) h

variable {V U} in

theorem cechTopIso_hom (h : ∀ i, U i ≤ V) : (cechTopIso R F h).hom =
    cechComplexMap (cechCubeRes R F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := rfl

@[simp]
theorem d_cechRestrictions (x : sectionsOn F V) :
    Cube.d (cechCube R F V U) 1 (cechRestrictions R F V U x) = 0 :=
  d_presheafCechAug (sectionsPresheaf R F) V U x

def toCechH : sectionsOn F V →ₗ[R] cechH R F V U 0 := presheafToCechH (sectionsPresheaf R F) V U

variable {V U} (hc : V ≤ ⨆ i, U i)

include hc in

theorem cechCube_exactAt_zero_one :
    (cubeComplex (cechCube R F V U)).ExactAt 0 ∧ (cubeComplex (cechCube R F V U)).ExactAt 1 :=
  presheafCube_exactAt_zero_one (T := X.toPresheafedSpace.carrier)
    (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem toCechH_bijective : Function.Bijective (toCechH R F V U) :=
  presheafToCechH_bijective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

def cechHZeroEquiv : cechH R F V U 0 ≃ₗ[R] sectionsOn F V :=
  (LinearEquiv.ofBijective _ (toCechH_bijective R F hc)).symm

@[simp]
theorem cechHZeroEquiv_symm_apply (x : sectionsOn F V) :
    (cechHZeroEquiv R F hc).symm x = toCechH R F V U x := rfl

@[simp]
theorem cechHZeroEquiv_toCechH (x : sectionsOn F V) :
    cechHZeroEquiv R F hc (toCechH R F V U x) = x := (cechHZeroEquiv R F hc).apply_symm_apply x

def cechHZeroEquivCohOn : cechH R F V U 0 ≃ₗ[R] cohOn F V 0 :=
  (cechHZeroEquiv R F hc).trans (cohOn.zeroEquiv R F V).symm

end Basic

section Scalars

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechAbCubeToCube :
    Cube.SemiHom (Int.castRingHom R) (cechAbCube F.presheaf V U) (cechCube R F V U) where
  app s :=
    { toFun := (sectionsOn.toΓ F (cechOpen V U s)).symm
      map_add' := map_add _
      map_smul' := fun n x => (map_zsmul (sectionsOn.toΓ F (cechOpen V U s)).symm n x).trans
        (Int.cast_smul_eq_zsmul R n _).symm }
  app_res _ _ := rfl

variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]

variable [LinearOrder ι]

def cechAbHEquiv (n : ℕ) : cechAbH F.presheaf V U n ≃+ cechH R F V U n :=
  AddEquiv.ofBijective ((cechAbCubeToCube R F V U).homology n).toAddMonoidHom
    ((cechAbCubeToCube R F V U).homology_bijective (fun _ _ => Function.bijective_id) n)

variable {F} in

theorem cechAbHEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R G V U n ((cechAbHMap V U φ.mapPresheaf n).hom x) =
      (cechHMap R V U φ n).hom (cechAbHEquiv R F V U n x) :=
  (cechAbCubeToCube R F V U).homology_naturality (cechAbCubeToCube R G V U)
    (cechAbCubeMap V U φ.mapPresheaf) (cechCubeMap R V U φ) (fun _ _ _ => rfl) n x

theorem cechAbHEquiv_toCechAbH (x : sectionsOn F V) :
    cechAbHEquiv R F V U 0 (toCechAbH F.presheaf V U (sectionsOn.toΓ F V x)) =
      toCechH R F V U x :=
  (cechAbCubeToCube R F V U).homology_cechAugHomology _

end Scalars

section Morphism

variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)

theorem preimage_cechOpen (s : Finset ι) :
    g ⁻¹ᵁ cechOpen V U s = cechOpen (g ⁻¹ᵁ V) (fun i => g ⁻¹ᵁ U i) s := by
  ext x
  exact mem_cechOpen.trans (mem_cechOpen (V := g ⁻¹ᵁ V) (U := fun i => g ⁻¹ᵁ U i)).symm

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)

def sectionsOn.mapOver (W : X.Opens) : sectionsOn F W →ₛₗ[σ] sectionsOn G (g ⁻¹ᵁ W) where
  toFun x := (sectionsOn.toΓ G (g ⁻¹ᵁ W)).symm (φ.app W (sectionsOn.toΓ F W x))
  map_add' x y := map_add (φ.app W).hom x y
  map_smul' r x := by
    have h : g.app W (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) =
        restrictGlobal Y (g ⁻¹ᵁ W) (algebraMap S Γ(Y, ⊤) (σ r)) := by
      rw [← hσ]
      exact ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) _
    refine (φ.app_smul (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) x).trans ?_
    exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) =>
      (a • (show Γ(G, g ⁻¹ᵁ W) from φ.app W (sectionsOn.toΓ F W x)) : Γ(G, g ⁻¹ᵁ W))) h

theorem sectionsOn.toΓ_mapOver (W : X.Opens) (x : sectionsOn F W) :
    sectionsOn.toΓ G (g ⁻¹ᵁ W) (sectionsOn.mapOver hσ φ W x) = φ.app W (sectionsOn.toΓ F W x) :=
  rfl

theorem sectionsOn.mapOver_res {W W' : X.Opens} (h : W' ≤ W) (x : sectionsOn F W) :
    sectionsOn.mapOver hσ φ W' (sectionsOn.res R F h x) =
      sectionsOn.res S G (g.preimage_mono h) (sectionsOn.mapOver hσ φ W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

def cechCubeMapOver :
    Cube.SemiHom σ (cechCube R F V U) (cechCube S G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i) where
  app s := (sectionsOn.res S G (preimage_cechOpen g V U s).ge).comp
    (sectionsOn.mapOver hσ φ (cechOpen V U s))
  app_res {s t} h x :=
    (congrArg (sectionsOn.res S G (preimage_cechOpen g V U t).ge)
      (sectionsOn.mapOver_res hσ φ (cechOpen_anti V U h) x)).trans
      ((sectionsOn.res_res S G _ _ _).trans
        (sectionsOn.res_res S G _ (cechOpen_anti _ _ h) _).symm)

theorem cechCubeMapOver_id_bijective (s : Finset ι) : Function.Bijective
    ((cechCubeMapOver V U hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))).app s) :=
  (sectionsOn.congrOpens S G (preimage_cechOpen g V U s)).bijective

variable [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

variable (G) in

def cechCubePushforwardIso : cechCube R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cechCube R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  Cube.isoMk (fun s => LinearEquiv.ofBijective _
    (cechCubeMapOver_id_bijective (σ := RingHom.id R) V U hg s))
    (cechCubeMapOver (σ := RingHom.id R) V U hg (𝟙 _)).app_res

variable (G) in

def cechPushforwardIso [LinearOrder ι] : cech R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cech R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  (cechFunctor ι R).mapIso (cechCubePushforwardIso V U G hg)

end Morphism

section Affine

variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)

def tildeToSections (W : (Spec A).Opens) : M →ₗ[A] sectionsOn (tilde M) W :=
  (sectionsOn.specEquiv (tilde M) W).symm.toLinearMap ∘ₗ (tilde.toOpen M W).hom

@[simp]
theorem res_tildeToSections {W W' : (Spec A).Opens} (h : W' ≤ W) (m : M) :
    sectionsOn.res A (tilde M) h (tildeToSections M W m) = tildeToSections M W' m := rfl

theorem isLocalizedModule_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) : IsLocalizedModule.Away f (tildeToSections M W) := by
  have h₀ : IsLocalizedModule.Away f (tilde.toOpen M W).hom := by
    subst h
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (tilde.toOpen M W).hom (sectionsOn.specEquiv (tilde M) W).symm

def awayTransition {a b : A} (h : a ∣ b) :
    LocalizedModule (.powers a) M →ₗ[A] LocalizedModule (.powers b) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd h (LocalizedModule.mkLinearMap _ M))

@[simp]
theorem awayTransition_mk_one {a b : A} (h : a ∣ b) (m : M) :
    awayTransition M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m

def sectionsAwayEquiv (f : A) {W : (Spec A).Opens} (h : W = PrimeSpectrum.basicOpen f) :
    sectionsOn (tilde M) W ≃ₗ[A] LocalizedModule (.powers f) M :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv (.powers f) (tildeToSections M W) (LocalizedModule.mkLinearMap _ M)

@[simp]
theorem sectionsAwayEquiv_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) (m : M) :
    sectionsAwayEquiv M f h (tildeToSections M W m) = LocalizedModule.mk m 1 :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv_apply (.powers f) _ _ m

variable (f g : A)

end Affine

end GlobalTheory

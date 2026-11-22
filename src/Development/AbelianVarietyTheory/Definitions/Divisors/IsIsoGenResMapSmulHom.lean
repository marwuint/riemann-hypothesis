import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)
open GlobalTheory.VB (IsVB IsFrame IsSubbundle Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.Vert

section Dim

attribute [local instance low] specializationOrder

theorem dim_add_dim_le {S T W : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace W] [QuasiSober S] [T0Space S] [QuasiSober T] [T0Space T] [QuasiSober W]
    [T0Space W] [IrreducibleSpace T] {f : S → T} (hf : IsClosedMap f) {j : W → S}
    (hj : Continuous j) (hi : Function.Injective j) (h : ∀ w, f (j w) = genericPoint T) :
    topologicalKrullDim W + topologicalKrullDim T ≤ topologicalKrullDim S := by
  have key (a : S) : Order.height (f a) ≤ Order.height a := by
    refine Order.height_le_iff'.2 fun p hp => ?_
    induction p using RelSeries.inductionOn' generalizing a with
    | singleton x => simp
    | snoc p x hx ih =>
      simp only [RelSeries.last_snoc] at hp
      subst hp
      have hx' : p.last < f a := hx
      obtain ⟨a', ha, e⟩ := hf.specializingMap (show f a ⤳ p.last from hx'.le)
      have hlt : a' < a := lt_of_le_of_ne ha fun h => hx'.ne (by rw [← e, h])
      grw [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, ih a' e.symm]
      exact Order.height_add_one_le hlt
  have key' (p : LTSeries W) :
      p.length + Order.height (genericPoint T) ≤ Order.height (j p.last) := by
    induction p using RelSeries.inductionOn' with
    | singleton x => simpa [h] using key (j x)
    | snoc p x hx ih =>
      have hx' : p.last < x := hx
      have hlt : j p.last < j x := lt_of_le_of_ne (Specializes.map hx'.le hj) (hi.ne hx'.ne)
      rw [RelSeries.last_snoc, RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, add_right_comm]
      exact (add_le_add_left ih 1).trans (Order.height_add_one_le hlt)
  have hT : topologicalKrullDim T = Order.height (genericPoint T) := by
    refine (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T))).trans ?_
    letI : OrderTop T := { top := genericPoint T, le_top := genericPoint_specializes }
    exact Order.height_top_eq_krullDim.symm
  rw [hT, show topologicalKrullDim W = Order.krullDim W from
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    show topologicalKrullDim S = Order.krullDim S from
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with _ | _
  · simp [Order.krullDim_eq_bot]
  rw [Order.krullDim_eq_iSup_length, ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_iSup
    (OrderTop.bddAbove _)]
  exact iSup_le fun p => (WithBot.coe_le_coe.2 (key' p)).trans (Order.height_le_krullDim _)

end Dim

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

namespace Model

namespace Hom

variable {Z Z₁ : Model O} (f : Hom Z₁ Z)

instance isProper : IsProper f.f := isProper_of_comp_str f.comp_str

def relDim (_ : Hom Z₁ Z) : ℕ := Z₁.relDim - Z.relDim

abbrev fnField (_ : Hom Z₁ Z) : Type := Z.X.residueField (genericPoint Z.X)

def genFibre : Scheme.{0} := f.f.fiber (genericPoint Z.X)

def genFibreι : f.genFibre ⟶ Z₁.X := f.f.fiberι _

def genFibreStr : f.genFibre ⟶ Sp f.fnField := f.f.fiberToSpecResidueField _

instance : Algebra f.fnField Γ(f.genFibre, ⊤) := algebraΓOfHom f.genFibreStr

theorem isPullback_genFibre :
    IsPullback f.genFibreι f.genFibreStr f.f (Z.X.fromSpecResidueField (genericPoint Z.X)) :=
  .of_hasPullback _ _

instance : IsProper f.genFibreStr := MorphismProperty.of_isPullback f.isPullback_genFibre f.isProper

instance : IsAffineHom f.genFibreι :=
  have : IsAffineHom (Z.X.fromSpecResidueField (genericPoint Z.X) ≫ Z.str) := inferInstance
  have : IsAffineHom (Z.X.fromSpecResidueField (genericPoint Z.X)) := .of_comp _ Z.str
  MorphismProperty.of_isPullback f.isPullback_genFibre.flip this

theorem dim_genFibre_add_le : topologicalKrullDim f.genFibre + (Z.relDim + 1 : ℕ) ≤
    (Z₁.relDim + 1 : ℕ) := by
  rw [← Z.dim_eq, ← Z₁.dim_eq]
  exact dim_add_dim_le f.f.isClosedMap f.genFibreι.continuous (f.f.fiberι _).isEmbedding.injective
    fun w => (f.f.range_fiberι _).le ⟨w, rfl⟩

instance : Nonempty f.genFibre :=
  have ⟨x, hx⟩ := f.f.surjective (genericPoint Z.X)
  ((f.f.range_fiberι _).ge hx).elim fun w _ => ⟨w⟩

theorem exists_dim_genFibre :
    ∃ n : ℕ, topologicalKrullDim f.genFibre = n ∧ n + Z.relDim ≤ Z₁.relDim := by
  have h := f.dim_genFibre_add_le
  have h₀ : topologicalKrullDim f.genFibre ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 inferInstance)
  generalize topologicalKrullDim f.genFibre = a at *
  lift a to ℕ∞ using h₀
  have h' : a + (Z.relDim + 1 : ℕ) ≤ (Z₁.relDim + 1 : ℕ) := by exact_mod_cast h
  lift a to ℕ using by rintro rfl; simp at h'
  have h'' : a + (Z.relDim + 1) ≤ Z₁.relDim + 1 := by exact_mod_cast h'
  exact ⟨a, rfl, by omega⟩

theorem dim_genFibre_le : topologicalKrullDim f.genFibre ≤ f.relDim := by
  obtain ⟨n, e, h⟩ := f.exists_dim_genFibre
  rw [e]
  exact_mod_cast Nat.le_sub_of_add_le h

theorem diffVanish_genFibre :
    DiffVanish (f.relDim + 1) (chiPic f.fnField (structureModule f.genFibre)) :=
  have ⟨_, hA⟩ := Z₁.exists_isAmpleLB
  (hA.pull_of_isAffineHom f.genFibreι).diffVanish_chiPic_of_isProper (f := f.genFibreStr)
    (fun _ => rfl) _ (suppDim_structureModule.trans_le f.dim_genFibre_le)

def fibreDeg : PicSym Z₁.X →ₗ[ℚ] ℚ :=
  picForm f.diffVanish_genFibre ∘ₗ (picSymPull f.genFibreι).toLinearMap

end Hom

variable (Z : Model O)

abbrev genRes : Z.X.Modules ⥤ Z.gen.toScheme.Modules := Scheme.Modules.pullback Z.gen.ι

abbrev GenIso (E E' : Z.X.Modules) : Type := Z.genRes.obj E ≅ Z.genRes.obj E'

variable {Z} {Z₁ : Model O} {E E' E'' : Z.X.Modules} {r : ℕ}

def genEquiv {V : Z.X.Opens} (h : V ≤ Z.gen) : Γ(Z.X, V) ≃+* Γ(Z.gen.toScheme, Z.gen.ι ⁻¹ᵁ V) :=
  haveI := Z.gen.ι.isIso_app V (h.trans Z.gen.opensRange_ι.ge)
  (asIso (Z.gen.ι.app V)).commRingCatIsoToRingEquiv

theorem genEquiv_apply {V : Z.X.Opens} (h : V ≤ Z.gen) (a : Γ(Z.X, V)) :
    genEquiv h a = (Z.gen.ι.app V).hom a := rfl

theorem isIso_genRes_map_smulHom (E : Z.X.Modules) {g : O} (hg : g ≠ 0) :
    IsIso (Z.genRes.map (smulHom E (Z.const g))) := by
  rw [VB.pullback_map_smulHom]
  have h : IsUnit (Z.gen.ι.appTop (Z.const g)) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top Z.gen.ι _).le (Z.gen_le_basicOpen hg x.2))
  exact (isUnit_iff_isIso _).1 (h.map (smulEnd _))

namespace GenIso

def ofHom (ψ : E' ⟶ E) [IsIso (Z.genRes.map ψ)] : Z.GenIso E E' := (asIso (Z.genRes.map ψ)).symm

variable (E) in

def smul (g : O) (hg : g ≠ 0) : Z.GenIso E E :=
  haveI := isIso_genRes_map_smulHom E hg
  ofHom (smulHom E (Z.const g))

theorem smul_inv (g : O) (hg : g ≠ 0) :
    (smul E g hg).inv = Z.genRes.map (smulHom E (Z.const g)) := rfl

section Pull

variable {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

def genMap : Z₁.gen.toScheme ⟶ Z.gen.toScheme := f.resLE _ _ (preimage_gen hf).ge

def genPullIso : Scheme.Modules.pullback f ⋙ Z₁.genRes ≅
    Z.genRes ⋙ Scheme.Modules.pullback (genMap hf) :=
  Scheme.Modules.pullbackComp _ f ≪≫
    Scheme.Modules.pullbackCongr (f.resLE_comp_ι (preimage_gen hf).ge).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm

def pull (φ : Z.GenIso E E') :
    Z₁.GenIso ((Scheme.Modules.pullback f).obj E) ((Scheme.Modules.pullback f).obj E') :=
  (genPullIso hf).app E ≪≫ (Scheme.Modules.pullback (genMap hf)).mapIso φ ≪≫
    ((genPullIso hf).app E').symm

theorem pull_inv {φ : Z.GenIso E E'} {ψ : E' ⟶ E} (h : φ.inv = Z.genRes.map ψ) :
    (φ.pull hf).inv = Z₁.genRes.map ((Scheme.Modules.pullback f).map ψ) := by
  simp only [pull, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, h,
    Category.assoc]
  exact NatIso.naturality_2 (genPullIso hf) ψ

theorem pull_smul (g : O) (hg : g ≠ 0) : (smul E g hg).pull hf = smul _ g hg :=
  Iso.ext (Iso.inv_eq_inv _ _ |>.1 (by
    rw [pull_inv hf (smul_inv g hg), VB.pullback_map_smulHom f, appTop_const hf, smul_inv]))

end Pull

variable (φ : Z.GenIso E E')

def detUnit (c : Chart E r) (c' : Chart E' r) [E.IsQuasicoherent] [E'.IsQuasicoherent]
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ (c.U ⊓ c'.U)) : Γ(Z.gen.toScheme, T)ˣ :=
  (c.isFrame.pullback Z.gen.ι).detUnit ((c'.isFrame.pullback Z.gen.ι).map_iso φ.inv)
    (h.trans (Z.gen.ι.preimage_mono inf_le_left)) (h.trans (Z.gen.ι.preimage_mono inf_le_right))

theorem detUnit_rel (c d : Chart E r) (c' d' : Chart E' r) [E.IsQuasicoherent]
    [E'.IsQuasicoherent] {V : Z.X.Opens} (hc : V ≤ c.U ⊓ c'.U) (hd : V ≤ d.U ⊓ d'.U)
    {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ V) :
    φ.detUnit c c' (h.trans (Z.gen.ι.preimage_mono hc)) =
      Units.map (Z.gen.ι.appLE V T h).hom.toMonoidHom
        (c.isFrame.detUnit d.isFrame (hc.trans inf_le_left) (hd.trans inf_le_left) *
          (c'.isFrame.detUnit d'.isFrame (hc.trans inf_le_right) (hd.trans inf_le_right))⁻¹) *
        φ.detUnit d d' (h.trans (Z.gen.ι.preimage_mono hd)) := by
  have e := c.isFrame.val_detUnit_pullback d.isFrame Z.gen.ι (hc.trans inf_le_left)
    (hd.trans inf_le_left) h
  have e' := c'.isFrame.val_detUnit_pullback d'.isFrame Z.gen.ι (hc.trans inf_le_right)
    (hd.trans inf_le_right) h
  rw [← (c'.isFrame.pullback Z.gen.ι).detUnit_map_iso _ φ.inv] at e'
  rw [map_mul, map_inv, ← Units.ext (v := Units.map _ _) e, ← Units.ext (v := Units.map _ _) e',
    mul_right_comm, detUnit, detUnit, IsFrame.detUnit_mul, eq_mul_inv_iff_mul_eq,
    IsFrame.detUnit_mul]

def div (hE : IsVB E r) (hE' : IsVB E' r) : VertDiv Z :=
  haveI := hE.isQuasicoherent
  haveI := hE'.isQuasicoherent
  .ofUnits (LB.div (det E r) (det E' r)) (Semi.LB.isLB_div hE.isLB_det hE'.isLB_det)
    (fun p => (genEquiv inf_le_left).symm
      (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)
    (fun _ => (Units.isUnit _).map _) fun p q => by
      have hV := (inf_le_left.trans inf_le_left : Z.gen ⊓ (LB.div (det E r) (det E' r)).U p ⊓
        (LB.div (det E r) (det E' r)).U q ≤ Z.gen)
      have H (p : (LB.div (det E r) (det E' r)).ι) (h) : genEquiv hV (resG Z.X h
          ((genEquiv inf_le_left).symm
            (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono inf_le_right)).val)) =
          (φ.detUnit p.1 p.2 (Z.gen.ι.preimage_mono (h.trans inf_le_right))).val := by
        rw [genEquiv_apply, Cartier.app_resG, ← genEquiv_apply inf_le_left,
          RingEquiv.apply_symm_apply]
        exact congrArg Units.val (IsFrame.res_detUnit _ _ _ _ _)
      refine (genEquiv hV).injective ?_
      refine (H p _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg _ (H q _))).symm)
      rw [φ.detUnit_rel p.1 q.1 p.2 q.2 (inf_le_left.trans inf_le_right)
        inf_le_right le_rfl, Units.val_mul]
      refine congrArg (· * _) ?_
      rw [genEquiv_apply, Scheme.Hom.app_eq_appLE, ← val_res]
      refine congrArg (fun u => (Z.gen.ι.appLE _ _ le_rfl).hom (Units.val u)) ?_
      change _ = res _ (res _ (IsFrame.detUnit _ _ _ _) * (res _ (IsFrame.detUnit _ _ _ _))⁻¹)
      simp only [map_mul, map_inv, IsFrame.res_detUnit]

variable (hE : IsVB E r) (hE' : IsVB E' r) (hE'' : IsVB E'' r)

theorem vCls_div : Z.vCls (φ.div hE hE').cls = cls _ hE.isLB_det - cls _ hE'.isLB_det :=
  (VertDiv.vCls_cls _).trans (cls_div _ _ _)

variable {φ} {ψ : E' ⟶ E}

end GenIso

end Model

structure Flag {X : Scheme.{0}} (E : X.Modules) (N : ℕ) where

  F : Fin (N + 1) → X.Modules

  ι : ∀ i, F i ⟶ E

  isSubbundle : ∀ i, IsSubbundle (ι i)

  isVB : ∀ i, IsVB (F i) i

  step : ∀ i : Fin N, F i.castSucc ⟶ F i.succ

  step_ι : ∀ i, step i ≫ ι i.succ = ι i.castSucc

  isIso_last : IsIso (ι (Fin.last N))

namespace Flag

variable {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N)

attribute [instance] isIso_last

attribute [reassoc (attr := simp)] step_ι

instance mono_ι (i : Fin (N + 1)) : Mono (fl.ι i) := (fl.isSubbundle i).mono

instance mono_step (i : Fin N) : Mono (fl.step i) := mono_of_mono_fac (fl.step_ι i)

include fl in

theorem isVB_self : IsVB E N := (fl.isVB (Fin.last N)).of_iso (asIso (fl.ι _))

def gr (i : Fin N) : X.Modules := cokernel (fl.step i)

def π (i : Fin N) : fl.F i.succ ⟶ fl.gr i := cokernel.π _

instance epi_π (i : Fin N) : Epi (fl.π i) := inferInstanceAs (Epi (cokernel.π _))

theorem isVB_cokernel (i : Fin (N + 1)) : IsVB (cokernel (fl.ι i)) (N - i) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨s, hs⟩ := (fl.isSubbundle i).isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk (fl.ι i) (cokernel.π _)
    (cokernel.condition _)) i s { exact := ShortComplex.exact_cokernel _ } (fl.isVB i) hs
  obtain rfl : s = N - i := by have := h.rank_unique fl.isVB_self; omega
  exact hs x

theorem isVB_gr (i : Fin N) : IsVB (fl.gr i) 1 := by
  refine VB.isVB_X₁_of_shortExact X _ 1 _ (shortExact_cokernel_comp (fl.step i) (fl.ι i.succ)) ?_
    (fl.isVB_cokernel i.succ)
  have h := (fl.isVB_cokernel i.castSucc).of_iso (cokernelIsoOfEq (fl.step_ι i).symm)
  rwa [show N - (i.castSucc : ℕ) = 1 + (N - (i.succ : ℕ)) by simp; omega] at h

def root (i : Fin N) : LB X := det (fl.gr i) 1

def ofIso {E' : X.Modules} (e : E ≅ E') : Flag E' N where
  F := fl.F
  ι i := fl.ι i ≫ e.hom
  isSubbundle i := ⟨inferInstance, _, (fl.isVB_cokernel i).of_iso (cokernelCompIsIso _ _).symm⟩
  isVB := fl.isVB
  step := fl.step
  step_ι i := fl.step_ι_assoc i _
  isIso_last := inferInstance

end Flag

namespace Model

variable {Z : Model O} {E E' : Z.X.Modules} {N : ℕ}

structure FlagPair (φ : Z.GenIso E E') (N : ℕ) where

  fl : Flag E N

  fl' : Flag E' N

  gen : ∀ i, Z.GenIso (fl.F i) (fl'.F i)

  gen_ι : ∀ i, (gen i).hom ≫ Z.genRes.map (fl'.ι i) = Z.genRes.map (fl.ι i) ≫ φ.hom

instance mono_genRes_map_ι (fl : Flag E N) (i : Fin (N + 1)) : Mono (Z.genRes.map (fl.ι i)) :=
  have := (fl.isVB i).isQuasicoherent
  have := fl.isVB_self.isQuasicoherent
  mono_pullback_map _ _

namespace FlagPair

variable {φ : Z.GenIso E E'} (P : FlagPair φ N)

theorem gen_step (i : Fin N) : Z.genRes.map (P.fl.step i) ≫ (P.gen i.succ).hom =
    (P.gen i.castSucc).hom ≫ Z.genRes.map (P.fl'.step i) := by
  rw [← cancel_mono (Z.genRes.map (P.fl'.ι i.succ)), Category.assoc, Category.assoc, gen_ι,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Flag.step_ι, Flag.step_ι, gen_ι]

def grIso (i : Fin N) : Z.GenIso (P.fl.gr i) (P.fl'.gr i) :=
  PreservesCokernel.iso Z.genRes (P.fl.step i) ≪≫
    cokernel.mapIso _ _ (P.gen i.castSucc) (P.gen i.succ) (P.gen_step i) ≪≫
      (PreservesCokernel.iso Z.genRes (P.fl'.step i)).symm

def div (i : Fin N) : VertDiv Z := (P.grIso i).div (P.fl.isVB_gr i) (P.fl'.isVB_gr i)

end FlagPair

structure FlagModel (φ : Z.GenIso E E') (N : ℕ) where

  B : Model O

  π : Hom B Z

  pair : FlagPair (φ.pull π.comp_str) N

def FlagModel.relDim {φ : Z.GenIso E E'} (M : FlagModel φ N) : ℕ := M.π.relDim

end Model

end GlobalTheory.Vert

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

open scoped TensorProduct

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens}

section Eigen

variable {O : Type} [CommRing O] (ρ : O →+* End F) (ρ' : O →+* End G) (ρ'' : O →+* End H)
  (σ : O →+* Γ(X, ⊤))

abbrev act (a : O) : F ⟶ F := ρ a

def IsEquivariant (φ : F ⟶ G) : Prop := ∀ a, act ρ a ≫ φ = φ ≫ act ρ' a

def eigenSub : Sub F := Sub.iInf fun a => Sub.ker (act ρ a - smulHom F (σ a))

def eigen : X.Modules := (eigenSub ρ σ).toMod

def eigenι : eigen ρ σ ⟶ F := (eigenSub ρ σ).incl

instance mono_eigenι : Mono (eigenι ρ σ) := (eigenSub ρ σ).mono_incl

variable {ρ σ} in

theorem mem_eigenSub_iff {s : Γ(F, V)} : s ∈ (eigenSub ρ σ).sec V ↔
    ∀ a, (act ρ a).app V s = resG X (le_top : V ≤ ⊤) (σ a) • s :=
  (Submodule.mem_iInf _).trans (forall_congr' fun _ => sub_eq_zero)

theorem eigenι_act (a : O) : eigenι ρ σ ≫ act ρ a = σ a • eigenι ρ σ := by
  ext V s : 3
  exact mem_eigenSub_iff.1 ((eigenSub ρ σ).incl_app_mem s) a

variable {ρ σ} in

def eigenLift (φ : G ⟶ F) (h : ∀ a, φ ≫ act ρ a = σ a • φ) : G ⟶ eigen ρ σ :=
  (eigenSub ρ σ).lift φ fun V s => mem_eigenSub_iff.2 fun a => congr(($(h a)).app V s)

@[reassoc (attr := simp)] theorem eigenLift_ι (φ : G ⟶ F) (h : ∀ a, φ ≫ act ρ a = σ a • φ) :
    eigenLift φ h ≫ eigenι ρ σ = φ := rfl

variable {ρ ρ'} in

def eigenMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) : eigen ρ σ ⟶ eigen ρ' σ :=
  eigenLift (eigenι ρ σ ≫ φ) fun a => by
    rw [Category.assoc, ← h a, ← Category.assoc, eigenι_act, Linear.smul_comp]

variable {ρ ρ'} in

@[reassoc (attr := simp)] theorem eigenMap_ι {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    eigenMap σ h ≫ eigenι ρ' σ = eigenι ρ σ ≫ φ := rfl

def eigenQuot : X.Modules :=
  cokernel (Sigma.desc fun a : O => act ρ a - smulHom F (σ a) : ∐ (fun _ : O => F) ⟶ F)

def eigenπ : F ⟶ eigenQuot ρ σ := cokernel.π _

instance epi_eigenπ : Epi (eigenπ ρ σ) := inferInstanceAs (Epi (cokernel.π _))

theorem act_eigenπ (a : O) : act ρ a ≫ eigenπ ρ σ = σ a • eigenπ ρ σ := by
  have := Sigma.ι (fun _ : O => F) a ≫= cokernel.condition
    (Sigma.desc fun a : O => act ρ a - smulHom F (σ a) : ∐ (fun _ : O => F) ⟶ F)
  rw [Sigma.ι_desc_assoc, comp_zero, Preadditive.sub_comp, sub_eq_zero, smulHom_comp] at this
  exact this

variable {ρ σ} in

def eigenDesc (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) : eigenQuot ρ σ ⟶ G :=
  cokernel.desc _ φ (Sigma.hom_ext _ _ fun a => by
    rw [Sigma.ι_desc_assoc, comp_zero, Preadditive.sub_comp, h a, smulHom_comp]
    exact sub_self _)

@[reassoc (attr := simp)] theorem eigenπ_desc (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenπ ρ σ ≫ eigenDesc φ h = φ := cokernel.π_desc _ _ _

instance isQuasicoherent_eigenQuot [F.IsQuasicoherent] : (eigenQuot ρ σ).IsQuasicoherent :=
  QCoh.isQuasicoherent_cokernel _

instance isFiniteQC_eigenQuot [IsFiniteQC F] : IsFiniteQC (eigenQuot ρ σ) :=
  QCoh.isFiniteQC_cokernel _

def dualAct : O →+* End (dual F) where
  toFun a := dualMap (act ρ a)
  map_one' := by rw [act, map_one]; exact dualMap_id
  map_mul' a b := by rw [act, mul_comm, map_mul]; exact dualMap_comp _ _
  map_zero' := by rw [act, map_zero]; exact dualMap_zero
  map_add' a b := by rw [act, map_add]; exact dualMap_add _ _

@[simp] theorem act_dualAct (a : O) : act (dualAct ρ) a = dualMap (act ρ a) := rfl

variable {ρ ρ'} in

theorem IsEquivariant.dual {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    IsEquivariant (dualAct ρ') (dualAct ρ) (dualMap φ) := fun a => by
  rw [act_dualAct, act_dualAct, ← dualMap_comp, ← dualMap_comp, h a]

theorem pullback_map_smulHom (f : Y ⟶ X) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (smulHom F a) = smulHom _ (f.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality _).symm.trans
    (smulHom_comp _ _)

theorem pullback_map_smul (f : Y ⟶ X) (a : Γ(X, ⊤)) (φ : F ⟶ G) :
    (Scheme.Modules.pullback f).map (a • φ) =
      (f.appTop a : Γ(Y, ⊤)) • (Scheme.Modules.pullback f).map φ := by
  rw [smul_hom_def, smul_hom_def, Functor.map_comp, pullback_map_smulHom]

def pullAct (f : Y ⟶ X) : O →+* End ((Scheme.Modules.pullback f).obj F) where
  toFun a := (Scheme.Modules.pullback f).map (act ρ a)
  map_one' := by rw [act, map_one]; exact CategoryTheory.Functor.map_id _ _
  map_mul' a b := by rw [act, map_mul]; exact Functor.map_comp _ _ _
  map_zero' := by rw [act, map_zero]; exact Functor.map_zero _ _ _
  map_add' a b := by rw [act, map_add]; exact Functor.map_add _

@[simp] theorem act_pullAct (f : Y ⟶ X) (a : O) :
    act (pullAct ρ f) a = (Scheme.Modules.pullback f).map (act ρ a) := rfl

variable {ρ ρ'} in

theorem IsEquivariant.pullback {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) (f : Y ⟶ X) :
    IsEquivariant (pullAct ρ f) (pullAct ρ' f) ((Scheme.Modules.pullback f).map φ) := fun a => by
  rw [act_pullAct, act_pullAct, ← Functor.map_comp, ← Functor.map_comp, h a]

def pullbackEigenHom (f : Y ⟶ X) : (Scheme.Modules.pullback f).obj (eigen ρ σ) ⟶
    eigen (pullAct ρ f) (f.appTop.hom.comp σ) :=
  eigenLift ((Scheme.Modules.pullback f).map (eigenι ρ σ)) fun a => by
    rw [act_pullAct, ← Functor.map_comp, eigenι_act, pullback_map_smul]; rfl

@[reassoc (attr := simp)] theorem pullbackEigenHom_ι (f : Y ⟶ X) :
    pullbackEigenHom ρ σ f ≫ eigenι _ _ = (Scheme.Modules.pullback f).map (eigenι ρ σ) := rfl

end Eigen

section Split

variable {O : Type} [CommRing O] {k : Type} [Field k] {ι : Type}

variable (X) in

abbrev scal [Algebra k Γ(X, ⊤)] (σ : O →+* k) : O →+* Γ(X, ⊤) := (algebraMap k Γ(X, ⊤)).comp σ

def splitMap (σ : ι → (O →+* k)) : k ⊗[ℤ] O →ₐ[k] (ι → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (ι → k)) (Pi.ringHom σ).toIntAlgHom
    fun _ _ => Commute.all _ _

@[simp] theorem splitMap_tmul (σ : ι → (O →+* k)) (c : k) (a : O) (j : ι) :
    splitMap σ (c ⊗ₜ a) j = c * σ j a := rfl

def IsSplitBy (σ : ι → (O →+* k)) : Prop := Function.Bijective (splitMap σ)

variable {σ : ι → (O →+* k)}

theorem IsSplitBy.injective (h : IsSplitBy σ) : Function.Injective σ := fun i j e => by
  classical
  by_contra hij
  have key (x : k ⊗[ℤ] O) : splitMap σ x i = splitMap σ x j := by
    induction x with
    | zero => simp
    | tmul c a => simp [e]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨x, hx⟩ := h.2 (Pi.single i 1)
  simpa [hx, Pi.single_apply, Ne.symm hij] using key x

theorem isSplitBy_of_injective [Fintype ι] [Module.Free ℤ O] [Module.Finite ℤ O]
    (hσ : Function.Injective σ) (hn : Module.finrank ℤ O = Fintype.card ι) : IsSplitBy σ := by
  have hs : Function.Surjective (splitMap σ).toLinearMap := by
    have hl : LinearIndependent k fun j => (σ j : O → k) :=
      (linearIndependent_monoidHom O k).comp (fun j => (σ j : O →* k))
        fun i j e => hσ (RingHom.ext fun a => DFunLike.congr_fun (F := O →* k) e a)
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_flip_eq_top_iff_linearIndependent.2 hl,
      Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, funext fun j => one_mul _⟩
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hn])).2 hs, hs⟩

variable [Algebra k Γ(X, ⊤)] (ρ : O →+* End F)

variable (k) in

def tensorAct : k ⊗[ℤ] O →+* End F :=
  letI : Algebra ℤ (End F) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.lift ((smulEnd F).comp (algebraMap k Γ(X, ⊤))).toIntAlgHom ρ.toIntAlgHom
    fun _ a => (smulHom_comp (act ρ a) _).symm).toRingHom

theorem act_tensorAct_tmul (c : k) (a : O) :
    act (tensorAct k ρ) (c ⊗ₜ a) = algebraMap k Γ(X, ⊤) c • act ρ a := rfl

theorem eigenι_tensorAct (j : ι) (x : k ⊗[ℤ] O) :
    eigenι ρ (scal X (σ j)) ≫ act (tensorAct k ρ) x =
      algebraMap k Γ(X, ⊤) (splitMap σ x j) • eigenι ρ (scal X (σ j)) := by
  induction x with
  | zero => simp only [act, map_zero, Pi.zero_apply, zero_smul]; exact comp_zero
  | tmul c a => rw [act_tensorAct_tmul, Linear.comp_smul, eigenι_act, splitMap_tmul, map_mul,
      mul_smul]; rfl
  | add x y hx hy =>
    rw [map_add, Pi.add_apply, map_add, add_smul, ← hx, ← hy, ← Preadditive.comp_add, act, map_add]

namespace IsSplitBy

variable [DecidableEq ι] (h : IsSplitBy σ)

def idem (j : ι) : k ⊗[ℤ] O := (AlgEquiv.ofBijective _ h).symm (Pi.single j 1)

@[simp] theorem splitMap_idem (j : ι) : splitMap σ (h.idem j) = Pi.single j 1 :=
  (AlgEquiv.ofBijective _ h).apply_symm_apply _

theorem tmul_mul_idem (j : ι) (a : O) :
    ((1 : k) ⊗ₜ[ℤ] a) * h.idem j = (σ j a ⊗ₜ[ℤ] (1 : O)) * h.idem j :=
  h.1 (funext fun i => by
    by_cases e : i = j <;> simp [e])

theorem idem_act (j : ι) (a : O) : act (tensorAct k ρ) (h.idem j) ≫ act ρ a =
    scal X (σ j) a • act (tensorAct k ρ) (h.idem j) := by
  have := congrArg (tensorAct k ρ) (h.tmul_mul_idem j a)
  rw [map_mul, map_mul] at this
  change _ ≫ act (tensorAct k ρ) _ = _ ≫ act (tensorAct k ρ) _ at this
  rw [act_tensorAct_tmul, act_tensorAct_tmul, map_one, one_smul, Linear.comp_smul, act, act,
    map_one] at this
  exact this.trans (congrArg _ (Category.comp_id _))

def proj (j : ι) : F ⟶ eigen ρ (scal X (σ j)) :=
  eigenLift (act (tensorAct k ρ) (h.idem j)) (h.idem_act ρ j)

theorem proj_ι (j : ι) : h.proj ρ j ≫ eigenι _ _ = act (tensorAct k ρ) (h.idem j) := rfl

@[reassoc (attr := simp)] theorem ι_proj (j : ι) : eigenι _ _ ≫ h.proj ρ j = 𝟙 _ := by
  rw [← cancel_mono (eigenι ρ (scal X (σ j))), Category.assoc, proj_ι, eigenι_tensorAct]
  simp

variable [Fintype ι]

end IsSplitBy

end Split

section Frobenius

variable (p : ℕ) [Fact p.Prime]

variable (X) in

def frob (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X := SS.FrobField.absFrob X p 1 Fact.out h

variable (h : (p : Γ(X, ⊤)) = 0)

@[simp] theorem frob_apply (x : X) : frob X p h x = x := rfl

@[simp] theorem frob_preimage (U : X.Opens) : frob X p h ⁻¹ᵁ U = U := rfl

theorem frob_app (U : X.Opens) (a : Γ(X, U)) : (frob X p h).app U a = (a ^ p : Γ(X, U)) :=
  congrArg (a ^ ·) (pow_one p)

theorem frob_appTop (a : Γ(X, ⊤)) : (frob X p h).appTop a = a ^ p := frob_app p h ⊤ a

@[reassoc] theorem frob_naturality (f : Y ⟶ X) (hY : (p : Γ(Y, ⊤)) = 0) :
    frob Y p hY ≫ f = f ≫ frob X p h := SS.FrobField.absFrob_nat f p 1 Fact.out hY h

abbrev frobPull : X.Modules ⥤ X.Modules := Scheme.Modules.pullback (frob X p h)

variable {O : Type} [CommRing O] {k : Type} [Field k] [CharP k p] [Algebra k Γ(X, ⊤)]

theorem frob_comp_scal (σ : O →+* k) :
    (frob X p h).appTop.hom.comp (scal X σ) = scal X ((frobenius k p).comp σ) :=
  RingHom.ext fun a => (frob_appTop p h _).trans (map_pow (algebraMap k Γ(X, ⊤)) (σ a) p).symm

def frobEigenHom (ρ : O →+* End F) (σ : O →+* k) : (frobPull p h).obj (eigen ρ (scal X σ)) ⟶
    eigen (pullAct ρ (frob X p h)) (scal X ((frobenius k p).comp σ)) :=
  eigenLift ((frobPull p h).map (eigenι ρ (scal X σ))) fun a => by
    rw [act_pullAct, ← Functor.map_comp, eigenι_act, pullback_map_smul, ← frob_comp_scal p h σ]
    rfl

@[reassoc (attr := simp)] theorem frobEigenHom_ι (ρ : O →+* End F) (σ : O →+* k) :
    frobEigenHom p h ρ σ ≫ eigenι _ _ = (frobPull p h).map (eigenι ρ (scal X σ)) :=
  eigenLift_ι _ _ _ _

end Frobenius

end GlobalTheory.VB

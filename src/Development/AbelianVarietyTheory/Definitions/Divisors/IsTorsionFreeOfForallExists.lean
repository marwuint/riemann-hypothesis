import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {r s : ℕ}

structure IsSubbundle (i : G ⟶ F) : Prop where

  mono : Mono i

  isVB_cokernel : ∃ s, IsVB (cokernel i) s

theorem isSubbundle_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsVB S.X₃ s) : IsSubbundle S.f :=
  ⟨hS.mono_f, s, h.of_iso (hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _))⟩

theorem isSubbundle_of_isIso (i : G ⟶ F) [IsIso i] : IsSubbundle i :=
  ⟨inferInstance, 0, isVB_zero_iff.2 (isZero_cokernel_of_epi i)⟩

theorem isSubbundle_inl (h : IsVB G s) : IsSubbundle (biprod.inl : F ⟶ F ⊞ G) :=
  isSubbundle_of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact h

theorem exists_app_eq_of_epi (φ : F ⟶ G) [Epi φ] (s : Γ(G, V)) {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (h : W ≤ V), x ∈ W ∧ ∃ t, φ.app W t = resM G h s := by
  obtain ⟨t, ht⟩ := QCoh.stalkLinear_surjective φ x (G.presheaf.germ V x hx s)
  obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hx t
  rw [QCoh.stalkLinear_germ, ← germ_resM hT hxT] at ht
  obtain ⟨T', hxT', i₁, i₂, e⟩ := G.presheaf.germ_eq x hxT hxT _ _ ht
  exact ⟨T', i₁.le.trans hT, hxT', resM F i₁.le t,
    (app_resM φ _ t).trans (e.trans (resM_resM hT i₂.le s))⟩

section Integral

variable [IsIntegral X]

theorem genericPoint_mem {x : X} (hx : x ∈ V) : genericPoint X ∈ V :=
  (genericPoint_specializes x).mem_open V.isOpen hx

variable (F) in

abbrev genStalk : Type := (F.presheaf.stalk (genericPoint X) :)

variable (F) in

def genRank : ℕ := Module.finrank X.functionField (genStalk F)

theorem genRank_congr (φ : F ≅ G) : genRank F = genRank G :=
  (QCoh.stalkLinearEquiv φ _).finrank_eq

theorem IsVB.genRank_eq (h : IsVB F r) : genRank F = r := h.finrank_stalk _

theorem genRank_eq_zero_iff [IsFiniteQC F] : genRank F = 0 ↔ genericPoint X ∉ QCoh.support F :=
  (Module.finrank_zero_iff (R := X.functionField)).trans QCoh.notMem_support_iff.symm

theorem genRank_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) [IsFiniteQC S.X₂] :
    genRank S.X₂ = genRank S.X₁ + genRank S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have e := (QCoh.exact_iff_stalkLinear S).1 hS.exact (genericPoint X)
  have h := LinearMap.finrank_range_add_finrank_ker (K := X.functionField)
    (stalkLinear S.g (genericPoint X))
  rw [LinearMap.range_eq_top.2 (QCoh.stalkLinear_surjective S.g _), finrank_top, e.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective S.f _)] at h
  exact h.symm.trans (add_comm _ _)

theorem genRank_cokernel (i : G ⟶ F) [Mono i] [h : IsFiniteQC F] :
    genRank F = genRank G + genRank (cokernel i) :=
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have := @genRank_shortExact _ _ _ hS h
  this

def Sub.ofGeneric (N : Submodule X.functionField (genStalk F)) : Sub F where
  sec V :=
    { carrier := {s | ∀ h : genericPoint X ∈ V, F.presheaf.germ V _ h s ∈ N}
      add_mem' := fun hs ht h => by rw [map_add]; exact add_mem (hs h) (ht h)
      zero_mem' := fun h => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs h => by rw [QCoh.germ_smul]; exact N.smul_mem _ (hs h) }
  res_mem h s hs hx := by rw [germ_resM]; exact hs (h hx)
  mem_of_local H hx := by
    obtain ⟨W, h, hxW, hs⟩ := H _ hx
    have := hs hxW
    rwa [germ_resM] at this

theorem Sub.mem_ofGeneric {N : Submodule X.functionField (genStalk F)} {s : Γ(F, V)} :
    s ∈ (Sub.ofGeneric N).sec V ↔ ∀ h : genericPoint X ∈ V, F.presheaf.germ V _ h s ∈ N := Iff.rfl

instance Sub.isQuasicoherent_ofGeneric [F.IsQuasicoherent]
    (N : Submodule X.functionField (genStalk F)) : (Sub.ofGeneric N).toMod.IsQuasicoherent := by
  refine Sub.isQuasicoherent _ fun U _ f t ht => ⟨1, ?_⟩
  by_cases hf : f = 0
  · rw [hf, pow_one, zero_smul]; exact zero_mem _
  · obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff f).1 hf)
    refine Submodule.smul_mem _ _ fun h => ?_
    have := ht (genericPoint_mem hx)
    rwa [germ_resM] at this

variable (F) in

def IsTorsionFree : Prop :=
  ∀ (V : X.Opens) (h : genericPoint X ∈ V) (s : Γ(F, V)), F.presheaf.germ V _ h s = 0 → s = 0

theorem isTorsionFree_of_forall_exists
    (H : ∀ (V : X.Opens) (h : genericPoint X ∈ V) (s : Γ(F, V)), F.presheaf.germ V _ h s = 0 →
      ∀ x ∈ V, ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ resM F h' s = 0) : IsTorsionFree F := by
  intro V hV s hs
  choose W hW hx h0 using fun x : V => H V hV s hs x x.2
  exact sec_ext_of_cover W hW (fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x =>
    (h0 x).trans (map_zero _).symm

theorem IsVB.isTorsionFree (h : IsVB F r) : IsTorsionFree F := by
  refine isTorsionFree_of_forall_exists fun V hV s hs x hx => ?_
  obtain ⟨U, e, -, hxU, hle, he⟩ := h.exists_affine hx
  have hU := genericPoint_mem hxU
  refine ⟨U, hle, hxU, ?_⟩
  obtain ⟨a, ha⟩ := (he U le_rfl).2 (resM F hle s)
  have h0 : ∑ i, X.presheaf.germ U _ hU (a i) • he.stalkBasis _ hU i = 0 := by
    rw [← hs, ← germ_resM hle hU, ← ha]
    simp only [Fintype.linearCombination_apply, map_sum, QCoh.germ_smul, resM_self,
      IsFrame.stalkBasis_apply]
  have h1 : a = 0 := funext fun i => germ_injective_of_isIntegral X _ hU
    ((Fintype.linearIndependent_iff.1 (he.stalkBasis _ hU).linearIndependent _ h0 i).trans
      (map_zero _).symm)
  rw [← ha, h1, map_zero]

def satSub (i : G ⟶ F) : Sub F := Sub.ofGeneric (LinearMap.range (stalkLinear i (genericPoint X)))

def sat (i : G ⟶ F) : X.Modules := (satSub i).toMod

def satι (i : G ⟶ F) : sat i ⟶ F := (satSub i).incl

instance mono_satι (i : G ⟶ F) : Mono (satι i) := (satSub i).mono_incl

def toSat (i : G ⟶ F) : G ⟶ sat i :=
  (satSub i).lift i fun _ s h => ⟨_, QCoh.stalkLinear_germ i _ h s⟩

@[reassoc (attr := simp)] theorem toSat_ι (i : G ⟶ F) : toSat i ≫ satι i = i := rfl

instance mono_toSat (i : G ⟶ F) [Mono i] : Mono (toSat i) := mono_of_mono_fac (toSat_ι i)

instance isQuasicoherent_sat (i : G ⟶ F) [F.IsQuasicoherent] : (sat i).IsQuasicoherent :=
  Sub.isQuasicoherent_ofGeneric _

instance isFiniteQC_sat [IsLocallyNoetherian X] (i : G ⟶ F) [IsFiniteQC F] : IsFiniteQC (sat i) :=
  .of_mono (satι i)

end Integral

section Curves

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]

structure IsProperCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProper : IsProper (strHom k C)

structure IsProjCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProjOver : IsProjOver (strHom k C)

structure IsSmoothProjCurve : Prop extends IsProjCurve k C where

  smooth : Smooth (strHom k C)

variable {k C}

omit [Field k] [Algebra k Γ(C, ⊤)] in

theorem suppDim_le_zero [IsIntegral C] (hd : topologicalKrullDim C = 1) {F : C.Modules} [IsFiniteQC F]
    (h : genRank F = 0) : QCoh.suppDim F ≤ 0 := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint C, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set C) = 1 := by
    rw [← hd, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq (zero_add 1).symm)

end Curves

section Degree

variable (k : Type) [Field k] [Algebra k Γ(X, ⊤)]

def degOfRank (F : X.Modules) (r : ℕ) : ℤ := chi k F - r * chi k (structureModule X)

theorem degOfRank_congr (φ : F ≅ G) : degOfRank k F r = degOfRank k G r := by
  rw [degOfRank, degOfRank, chi_congr k φ]

variable [IsIntegral X]

def deg (F : X.Modules) : ℤ := degOfRank k F (genRank F)

theorem deg_def : deg k F = chi k F - genRank F * chi k (structureModule X) := rfl

theorem deg_congr (φ : F ≅ G) : deg k F = deg k G := by
  rw [deg, deg, genRank_congr φ, degOfRank_congr k φ]

@[simp] theorem deg_structureModule : deg k (structureModule X) = 0 := by
  rw [deg_def, (isVB_structureModule X).genRank_eq]; simp

variable {k}

namespace IsProjCurve

end IsProjCurve

variable (k) in

def degLB (L : LB X) : ℤ := deg k (toMod L)

variable {L M N : LB X}

theorem degLB_eq (hL : L.IsLB) : degLB k L = chi k (toMod L) - chi k (structureModule X) := by
  rw [degLB, deg_def, (isVB_toMod hL).genRank_eq]; simp

theorem degLB_congr (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M) : degLB k L = degLB k M :=
  (LB.nonempty_iso_of_lbIso hL hM h).elim (deg_congr k)

theorem IsProjCurve.degLB_eq_interNum (hC : IsProjCurve k X) (hL : L.IsLB) :
    degLB k L = interNum k (structureModule X) ![L] := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have hd := CechPic.isLB_dual hL
  have e₁ := interNum_one_of_cls_eq_add (k := k) hA hC.dim_eq (LB.isLB_triv X) hd hL
    (CechPic.cls_dual_add hL).symm
  have e₂ : interNum k (structureModule X) ![LB.triv X] = 0 :=
    interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv X)) 0 rfl
  have e₃ : interNum k (structureModule X) ![CechPic.dual L] =
      chi k (structureModule X) - chi k (twist (structureModule X) L) :=
    (interNum_cons_of_cls_eq_neg k _ (P := ![]) hd isEmptyElim hL
      (by rw [CechPic.cls_dual hL, neg_neg])).trans
      (congrArg₂ (· - ·) (interNum_of_isEmpty k _ _) (interNum_of_isEmpty k _ _))
  rw [degLB_eq hL, ← chi_congr k (Twist.unitTwistIso L)]
  change chi k (twist (structureModule X) L) - _ = _
  omega

theorem IsProjCurve.degLB_of_cls_eq_add (hC : IsProjCurve k X) (hN : N.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) (e : CechPic.cls N hN = CechPic.cls L hL + CechPic.cls M hM) :
    degLB k N = degLB k L + degLB k M := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  rw [hC.degLB_eq_interNum hN, hC.degLB_eq_interNum hL, hC.degLB_eq_interNum hM]
  exact interNum_one_of_cls_eq_add hA hC.dim_eq hN hL hM e

def IsProjCurve.degPic (hC : IsProjCurve k X) : CechPic.Pic X →+ ℤ :=
  AddMonoidHom.mk' (Quotient.lift (fun L => degLB k L.1) fun L M h => degLB_congr L.2 M.2 h)
    fun a b => by
      obtain ⟨L, hL, rfl⟩ := CechPic.cls_surj a
      obtain ⟨M, hM, rfl⟩ := CechPic.cls_surj b
      exact hC.degLB_of_cls_eq_add (CechPic.isLB_tens hL hM) hL hM rfl

@[simp] theorem IsProjCurve.degPic_cls (hC : IsProjCurve k X) (hL : L.IsLB) :
    hC.degPic (CechPic.cls L hL) = degLB k L := rfl

namespace IsMaxSubDeg

end IsMaxSubDeg

end Degree

section Line

open ProjSpace ProjCoh

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k]

theorem isSmoothProjCurve_line : IsSmoothProjCurve k (PSpace k 1) := by
  have e := strHom_eq (algebraMap_top_eq k 1)
  refine ⟨⟨inferInstance, topologicalKrullDim_eq k 1, e ▸ isProjOver_str k 1⟩, e ▸ ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := @RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) (chartCover k 1)
    fun (i : Fin (1 + 1)) => ?_
  change Smooth (chartι k 1 i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
  exact RingHom.smooth_algebraMap.2
    (⟨inferInstance, inferInstance⟩ : Algebra.Smooth k (MvPolynomial {j // j ≠ i} k))

end Line

end GlobalTheory.VB
